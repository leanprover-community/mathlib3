import dynamics.topological.compact_metrizable
import dynamics.topological.topological_dynamics_basic

/-noncomputable theory-/


namespace topological_pressure
open topological_dynamics_basic


variables {X : Type} (T : X → X) [top_dyn_sys X T]


/-Nomenclature à revoir ?-/

def is_n_V_separated (n : ℕ) (V : set (X × X)) (V_uni : V ∈ uniformity X) (s : finset X) :
  Prop :=
∀ (x y : X), x ∈ s → y ∈ s → x ≠ y → ∀ k ≤ n, (T^[k] x) ∉ uniform_space.ball (T^[k] y) V


/-def n_V_entropy (n : ℕ) (V : set (X × X)) (V_uni : V ∈ uniformity X) :=
  Sup { Σ (x ∈ s), 1 : s : finset X, is_n_V_separated X T n V V_uni s } -/

lemma n_V_separated_mono_n (m n : ℕ) (V : set (X × X)) (V_uni : V ∈ uniformity X) (s : finset X) :
  m ≤ n → (is_n_V_separated T n V V_uni s) → (is_n_V_separated T m V V_uni s) :=
begin
  intros m_le_n n_V_separated x y x_in_s y_in_s x_ne_y k k_le_m,
  exact n_V_separated x y x_in_s y_in_s x_ne_y k (le_trans k_le_m m_le_n),
end


lemma n_V_separated_mono_V (n : ℕ) (V W : set (X × X)) (V_uni : V ∈ uniformity X) (W_uni : W ∈ uniformity X) (s : finset X) :
  W ⊆ V → (is_n_V_separated T n V V_uni s) → (is_n_V_separated T n W W_uni s) :=
begin
  intros W_sub_V n_V_separated x y x_in_s y_in_s x_ne_y k k_le_m,
  apply set.not_mem_subset (ball_mono W_sub_V (T^[k] y)),
  exact n_V_separated x y x_in_s y_in_s x_ne_y k k_le_m,
end


/- Fonction Card : n_V_separated finset X -> N. -/
/- MQ cette fonction est bornée (Lebesgue number lemma, version uniform spaces ?). -/
/- Son max est une fonction h(n, V). -/
/- MQ monotone en n, V (bonne inclusions). -/

def is_n_V_covering (n : ℕ) (V : set (X × X)) (V_uni : V ∈ uniformity X) (s : finset X) :
  Prop :=
∀ (x : X), ∃ y ∈ s, ∀ k ≤ n, (T^[k] x) ∈ uniform_space.ball (T^[k] y) V


lemma n_V_covering_mono_n (m n : ℕ) (V : set (X × X)) (V_uni : V ∈ uniformity X) (s : finset X) :
  m ≤ n → (is_n_V_covering T n V V_uni s) → (is_n_V_covering T m V V_uni s) :=
begin
  intros m_le_n n_V_covering x,
  specialize n_V_covering x,
  rcases n_V_covering with ⟨ y, y_in_s, y_close_orbit ⟩,
  use [y, y_in_s],
  intros k k_le_m,
  specialize y_close_orbit k (le_trans k_le_m m_le_n),
  exact y_close_orbit,
end


lemma n_V_covering_mono_V (n : ℕ) (V W : set (X × X)) (V_uni : V ∈ uniformity X) (W_uni : W ∈ uniformity X) (s : finset X) :
  W ⊆ V → (is_n_V_covering T n W W_uni s) → (is_n_V_covering T n V V_uni s) :=
begin
  intros W_sub_V n_V_covering x,
  specialize n_V_covering x,
  rcases n_V_covering with ⟨ y, y_in_s, y_close_orbit ⟩,
  use [y, y_in_s],
  intros k k_le_n,
  specialize y_close_orbit k k_le_n,
  apply ball_mono W_sub_V (T^[k] y),
  exact y_close_orbit,
end


/- totally_bounded -/

lemma finite_cover_balls_of_uniform_compact {α : Type} [uniform_space α] {s : set α}
  (hs : is_compact s) {V : set (α × α)} (V_uni : V ∈ uniformity α) :
  ∃t ⊆ s, set.finite t ∧ s ⊆ ⋃x∈t, uniform_space.ball x V :=
begin
  rcases ((filter.has_basis.mem_iff uniformity_has_basis_open).1 V_uni) with ⟨W, ⟨W_uni, W_open⟩, W_sub_V⟩,
  simp at W_sub_V,
  suffices : ∃t ⊆ s, set.finite t ∧ s ⊆ ⋃x∈t, uniform_space.ball x W,
  { rcases this with ⟨t, t_sub_s, ht⟩,
    use [t, t_sub_s, ht.1],
    apply @set.subset.trans _ s _ (⋃ (x : α) (H : x ∈ t), uniform_space.ball x V) ht.2,
    apply set.Union_mono,
    intro x,
    apply set.Union_mono,
    intro x_in_t,
    exact ball_mono W_sub_V x },
  apply hs.elim_finite_subcover_image,
  { intros x x_in_s,
    exact uniform_space.is_open_ball x W_open },
  { intros x xs,
    simp,
    use x,
    exact ⟨xs, uniform_space.mem_ball_self x W_uni⟩ }
end





end topological_pressure
