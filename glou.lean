import topology.instances.real
import topology.instances.ennreal
import init.algebra.classes
import topology.algebra.ordered.basic

open set
open filter
open_locale topological_space

@[simp]
lemma filter.not_eventually_false {α : Type*} (f : filter α) [ne_bot f] : ¬ (∀ᶠ x in f, false) :=
λ h, ne_bot.ne' (eventually_false_iff_eq_bot.mp h)

open filter
lemma tendsto_ge_of_incr {σ τ : Type*} [semilattice_sup σ] [linear_order τ]
   [topological_space τ] [order_topology τ]
  {s : σ → τ} {l : τ} (h_incr : monotone s) (h_lim : tendsto s at_top (𝓝 l)) :
    ∀ n , s n ≤ l :=
begin
  intros m₀ ,
  by_contra over_lim,
  have yes : ∀ᶠ n in at_top, s n ∈ Iio (s m₀),
    from h_lim (Iio_mem_nhds $ not_le.1 over_lim),
  have no : ∀ᶠ n in at_top, s n ∉ Iio (s m₀),
  { suffices : ∃ a, ∀ n ≥ a, s m₀ ≤ s n,
    { cases this with a ha ,
      have eq : { n | s m₀ ≤ s n } = { n | s n ∉ Iio (s m₀) }
        := by simp only [mem_Iio, not_lt] ,
      have at_least : Ici a ⊆ { n | s n ∉ Iio (s m₀) } := by rwa ← eq ,
      exact at_top.sets_of_superset (mem_at_top a) at_least , } ,
    exact ⟨m₀, λ b hb, h_incr hb⟩ , },
  haveI : nonempty σ := ⟨m₀⟩,
  haveI : (at_top : filter σ).ne_bot := infer_instance,
  simpa only [and_not_self, not_eventually_false] using yes.and no,
end

lemma tendsto_ge_of_incr_R' (s : ℕ → ℝ) (l : ℝ) (incr : monotone s) (lim : tendsto s at_top (𝓝 l)) :
    ∀ n , s(n) ≤ l := by library_search --works

lemma tendsto_ge_of_decr_R' (s : ℕ → ℝ) (l : ℝ) (decr : @monotone ℕ (order_dual ℝ) _ _ s) (lim : tendsto s at_top (𝓝 l)) :
    ∀ n , l ≤ s(n) := tendsto_ge_of_incr decr lim --does not work

lemma tendsto_ge_of_incr_ennreal'
  (s : ℕ → ennreal) (l : ennreal) (incr : monotone s) (lim : tendsto s at_top (𝓝 l)) :
  ∀ n , s(n) ≤ l := tendsto_ge_of_incr incr lim --does not work
