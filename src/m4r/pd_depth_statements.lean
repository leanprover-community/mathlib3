import tactic ring_theory.localization m4r.projective_resolution linear_algebra.free_module
  m4r.depth

universe u
open is_projective
open_locale classical
set_option old_structure_cmd true
/-- source: https://leanprover-community.github.io/archive/stream/116395-maths/topic
  /Error.20when.20applying.20supr_le.html-/

structure subcomplex {R : Type u} [ring R] (C : chain_complex ℤ (Module R)) :=
(complex : chain_complex ℤ (Module R))
(f : complex ⟶ C)
(f_inj : ∀ n : ℤ, linear_map.ker (f.f n : complex.X n →ₗ[R] C.X n) = ⊥)

instance chain_complex.has_zero {R : Type u} [ring R] : has_zero (chain_complex ℤ (Module R)) :=
⟨{ X := λ n, 0,
  d := λ i j, 0,
  d_comp_d := λ i j k, rfl,
  d_eq_zero := λ i j h, rfl }⟩

instance subcomplex.has_zero {R : Type u} [ring R] (C : chain_complex ℤ (Module R)) :
  has_zero (subcomplex C) :=
⟨{ complex := 0,
   f := 0,
   f_inj := λ n, eq_bot_iff.2 sorry}⟩

noncomputable def projective_resolution_len (R : Type u) [ring R] (M : Type u)
  [add_comm_group M] [module R M] (F : projective_resolution R M) :
  enat := enat.find (λ n, ∀ m, n < m → subsingleton (F.complex.X m))

noncomputable def projective_dimension (R : Type u) [ring R] (M : Module R) :=
  infi (projective_resolution_len R M)

noncomputable def global_dimension (R : Type u) [ring R] : enat :=
  supr (projective_dimension R)

def is_prime_ideal_chain {R : Type u} [comm_ring R]
  ( c : list (prime_spectrum R) ) : Prop :=
    c ≠ list.nil ∧ c.chain' (λ x y, x.as_ideal < y.as_ideal)

def prime_ideal_chain (R : Type u) [comm_ring R] :=
  {C : list (prime_spectrum R) // is_prime_ideal_chain C}

def prime_ideal_chain_len (R : Type u) [comm_ring R] (C : prime_ideal_chain R) : enat :=
enat.coe_hom (C.val.length - 1)

noncomputable def krull_dim (R : Type u) [comm_ring R] : enat :=
  supr (prime_ideal_chain_len R)

noncomputable def prime_codim {R : Type u} [comm_ring R] (P : ideal R) [P.is_prime] : enat :=
  krull_dim (localization.at_prime P)

noncomputable def codim {R : Type u} [comm_ring R] (I : ideal R) : enat :=
  enat.find (λ n, ∃ (P : ideal R) [P.is_prime], I ≤ P ∧ @prime_codim _ _ P (by assumption) = n)

lemma fg_of_top (R : Type u) [comm_ring R] :
  submodule.fg (⊤ : ideal R) :=
⟨set.to_finset (1 : set R), by rw set.coe_to_finset;
  exact ideal.span_singleton_one⟩

theorem depth_le_codim {R : Type u} [comm_ring R] [is_noetherian_ring R] (I : ideal R) :
  (depth I (⊤ : submodule R R) (fg_of_top R) : enat) ≤ codim I := sorry

def KD_le_n' (R : Type u) [comm_ring R] (n : ℕ) : Prop :=
  krull_dim R ≤ n

def KD_le_n (R : Type u) [comm_ring R] (n : ℕ) : Prop :=
  ∀ x : prime_ideal_chain R, prime_ideal_chain_len R x ≤ n

theorem le_equiv {R : Type u} [comm_ring R] {n : ℕ} :
  KD_le_n R n ↔ KD_le_n' R n :=
by rw [KD_le_n, KD_le_n', krull_dim, supr_le_iff]

/-- stolen shit ends -/
theorem finite_krull_dim_of_noetherian_local (R : Type u) [comm_ring R]
  [is_noetherian_ring R] [local_ring R] : ∃ n : ℕ, krull_dim R = n := sorry

noncomputable def krull_dim_of_noetherian_local (R : Type u) [comm_ring R] [is_noetherian_ring R]
  [local_ring R] : ℕ := nat.find (finite_krull_dim_of_noetherian_local R)

class is_system_of_params (R : Type u) [comm_ring R] [is_noetherian_ring R]
  [local_ring R] (s : set R) [fintype s] :=
(card : ∀ (t : set R) [fintype t], ideal.span t = local_ring.maximal_ideal R →
  fintype.card s ≤ fintype.card t)
(span : ideal.span s = local_ring.maximal_ideal R)

class is_regular_local (R : Type u) [comm_ring R]
  extends is_noetherian_ring R, local_ring R :=
(exists_params : ∃ (s : set R) [fintype s] [is_system_of_params R s],
  fintype.card s = krull_dim_of_noetherian_local R)

structure free_resolution (R : Type u) [ring R] (M : Type u) [add_comm_group M]
  [module R M] extends projective_resolution R M :=
(basis : Π n : ℤ, set (complex.X n))
(is_basis : ∀ n : ℤ, is_basis R (λ x : basis n, (x : complex.X n)))

class free_resolution.is_minimal (R : Type u) [comm_ring R] [local_ring R] (M : Type u)
  [add_comm_group M] [module R M] (F : free_resolution R M) : Prop :=
(d_cond : ∀ m n : ℤ, (F.complex.d m n).range
  ≤ local_ring.maximal_ideal R • (⊤ : submodule R (F.complex.X n)))

theorem free_resolution.exists_minimal (R : Type u) [comm_ring R] [local_ring R] (M : Type u)
  [add_comm_group M] [module R M] :
  ∃ (F : free_resolution R M), free_resolution.is_minimal R M F := sorry

noncomputable def free_resolution.minimal (R : Type u) [comm_ring R] [local_ring R] (M : Type u)
  [add_comm_group M] [module R M] : free_resolution R M :=
classical.some (free_resolution.exists_minimal R M)

instance free_resolution.minimal_spec (R : Type u) [comm_ring R] [local_ring R]
  (M : Type u) [add_comm_group M] [module R M] :
  free_resolution.is_minimal R M (free_resolution.minimal R M) :=
classical.some_spec (free_resolution.exists_minimal R M)

theorem projective_dim_eq_minimal_length (R : Type u) [comm_ring R] [local_ring R] {M : Type u}
  [add_comm_group M] [module R M] (N : submodule R M) (hfg : N.fg) :
  projective_dimension R N = projective_resolution_len R N
    (free_resolution.minimal R N).to_projective_resolution := sorry

variables (A : Type u)

def cochain_complex.to_chain_complex {R : Type u} [ring R] (C : cochain_complex ℤ (Module R)) :
  chain_complex ℤ (Module R) :=
{ X := λ n, C.X (-n),
  d := λ m n, C.d (-m) (-n),
  d_comp_d := λ i j k, C.d_comp_d _ _ _,
  d_eq_zero := λ i j h, C.d_eq_zero (λ (hij : -i + 1 = _), h
    (show _ = j + 1, by omega)) }

def chain_complex.to_cochain_complex {R : Type u} [ring R] (C : chain_complex ℤ (Module R)) :
  cochain_complex ℤ (Module R) :=
{ X := λ n, C.X (-n),
  d := λ m n, C.d (-m) (-n),
  d_comp_d := λ i j k, C.d_comp_d _ _ _,
  d_eq_zero := λ i j h, C.d_eq_zero (λ (hij : _ = -j + 1), h
    (show i + 1 = _, by omega)) }

-- where is this?!
instance residue_field.module (R : Type u) [comm_ring R] [local_ring R] :
  module R (local_ring.residue_field R) :=
by dunfold local_ring.residue_field; apply_instance

noncomputable def Koszul_subcomplex (R : Type u) [comm_ring R] [is_noetherian_ring R]
  [local_ring R] (s : set R) [fintype s] [is_system_of_params R s]
  (sf : fin (fintype.card s) → R) (hs : set.range sf = s) :
  Π n : ℕ, fintype.card s = n
  → subcomplex (free_resolution.minimal R (local_ring.residue_field R)).complex
| 0 h0 := 0
| (n+1) hn :=
{ complex := (inductive_Koszul R n (function.comp sf (fin.cast hn.symm))).to_chain_complex,
  f := sorry,
  f_inj := sorry }

def is_regular_local.params (R : Type u) [comm_ring R] [is_regular_local R] :
 set R := classical.some is_regular_local.exists_params

noncomputable instance is_regular_local.params_fintype
  (R : Type u) [comm_ring R] [is_regular_local R] :
  fintype (is_regular_local.params R) :=
classical.some (classical.some_spec is_regular_local.exists_params)

noncomputable instance is_regular_local.is_system_of_params
  (R : Type u) [comm_ring R] [is_regular_local R] :
  is_system_of_params R (is_regular_local.params R) :=
classical.some (classical.some_spec (classical.some_spec is_regular_local.exists_params))

instance integral_domain_of_is_regular_local (R : Type u) [h : comm_ring R]
  [is_regular_local R] : integral_domain R :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
  begin
    cases finite_krull_dim_of_noetherian_local R with n hdn,
    unfreezingI {revert R},
    induction n with n hn,
    { sorry },
    { sorry },
  end,
  ..h }

theorem finite_global_dim_of_is_regular_local (R : Type u) [comm_ring R] [is_regular_local R] :
  ∃ n : ℕ, global_dimension R = n := sorry

/-- The Auslander-Buchsbaum Formula -/
theorem projective_dimension_eq_depth_sub_depth (R : Type u) [comm_ring R] [local_ring R]
  [is_noetherian_ring R] (M : Type u) [add_comm_group M] [module R M] (n : ℕ)
  (hn : projective_dimension R (Module.of R M) = n) (hfg : submodule.fg (⊤ : submodule R M)) :
  (depth (local_ring.maximal_ideal R) (⊤ : submodule R R) (fg_of_top R) : ℤ)
    - depth (local_ring.maximal_ideal R) (⊤ : submodule R M) hfg = n := sorry

/-- The statement of the harder direction of the Auslander-Buchsbaum-Serre Theorem. -/
instance is_regular_local_of_finite_global_dim (R : Type u) [comm_ring R] [local_ring R]
  [is_noetherian_ring R] (n : ℕ) (h : global_dimension R = n) : is_regular_local R := sorry

instance is_regular_local.localization {R S : Type u} [comm_ring R] [comm_ring S]
  (P : ideal R) [ideal.is_prime P] (f : localization_map.at_prime S P)
  [is_regular_local R] :
  is_regular_local S :=
sorry
