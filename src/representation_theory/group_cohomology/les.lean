import .functorialityness
import .LTE.les_homology
open category_theory
noncomputable theory
universes v u

variables {k G : Type u} [comm_ring k] [group G] {A B C : Rep k G}
  (f : A ⟶ B) (g : B ⟶ C)

lemma Rep.mono_iff_injective : mono f ↔ function.injective f.hom :=
concrete_category.mono_iff_injective_of_preserves_pullback f

lemma Rep.epi_iff_surjective : epi f ↔ function.surjective f.hom :=
⟨by introI h; exact (Module.epi_iff_surjective f.hom).1
    (preserves_epi_of_preserves_colimit (Action.forget _ _) f),
λ h, concrete_category.epi_of_surjective _ (λ x, by rcases (h x); exact ⟨w, h_1⟩)⟩

lemma Rep.exact_iff : exact f g ↔ exact f.hom g.hom :=
⟨(Action.forget _ _).map_exact _ _, (Action.forget _ _).exact_of_exact_map⟩

namespace group_cohomology

def map_chain_map := pair_chain_map B A (monoid_hom.id G) f.hom (rep_hom_pair f)

lemma map_chain_map_f_apply {n : ℕ} (x : (fin n → G) → A) (i : fin n → G) :
  (map_chain_map f).f n x i = f.hom (x i) := rfl

lemma weehee (H : short_exact f g) (n : ℕ) :
  short_exact ((map_chain_map f).f n) ((map_chain_map g).f n) :=
by rcases H; exact
{ mono := (Module.mono_iff_injective _).2 $ λ x y h, funext $ λ i,
  begin
    rw Rep.mono_iff_injective at H_mono,
    replace h := function.funext_iff.1 h i,
    exact H_mono h,
  end,
  epi := concrete_category.epi_of_surjective _ $ λ x,
  begin
    rw Rep.epi_iff_surjective at H_epi,
    exact ⟨λ i, classical.some (H_epi (x i)), funext $ λ i, classical.some_spec (H_epi (x i))⟩,
  end,
  exact :=
  begin
    rw Rep.exact_iff at H_exact,
    rw Module.exact_iff at H_exact ⊢,
    ext,
    split,
    { rintros ⟨y, rfl⟩,
      ext,
      simp only [linear_map.mem_ker, map_chain_map, pair_chain_map_f_apply],
      exact linear_map.ext_iff.1 (linear_map.range_le_ker_iff.1 (le_of_eq H_exact)) _ },
    { rintro (h : _ = _),
      replace h : ∀ i : fin n → G, x i ∈ f.hom.range := λ i, by
        rw H_exact; exact function.funext_iff.1 h i,
      exact ⟨λ i, classical.some (h i), funext $ λ i, classical.some_spec (h i)⟩ }
  end }

def six_term_exact_seq (H : short_exact f g) (i j : ℕ) (hij : i + 1 = j) :
    exact_seq (Module.{u} k) [
    group_cohomology_map f i,
    group_cohomology_map g i,
    @homological_complex.δ (Module k) _ _ ℕ (complex_shape.up ℕ)
      _ _ _ (map_chain_map f) (map_chain_map g) (weehee f g H) i j hij,
    group_cohomology_map f j,
    group_cohomology_map g j
  ] :=
homological_complex.six_term_exact_seq _ _ _ _ _ _

end group_cohomology
