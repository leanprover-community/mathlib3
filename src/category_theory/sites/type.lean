import Kenny.sites.basic category_theory.limits.types

universes u v

namespace category_theory

instance has_pullback_Type : has_pullback (Type u) :=
λ F, by apply_instance

instance has_site_Type : has_site (Type u) :=
{ cov := λ α, { S | ∀ x : α, ∃ (f : Σ β, β ⟶ α), ∃ hf : f ∈ S, x ∈ set.range f.2},
  iso_mem := λ α β e x, ⟨⟨β, e.1⟩, set.mem_singleton _, e.2 x, congr_fun e.4 x⟩,
  comp_mem := λ α S HS F HF x, let ⟨f, hf, p, hfpx⟩ := HS x in
    let ⟨g, hg, q, hgqp⟩ := HF f hf p in
    ⟨⟨g.1, g.2 ≫ f.2⟩, ⟨f, hf, g, hg, rfl⟩, q, hfpx ▸ hgqp ▸ rfl⟩,
  pullback_mem := λ α S HS β f x, let ⟨g, hg, p, hgpx⟩ := HS (f x) in
    ⟨⟨pullback f g.2, pullback.fst f g.2⟩, ⟨g, hg, rfl⟩,
      ⟨λ v, pullback_diagram.rec_on v x p (f x),
      by intros v w h; cases h; dsimp only [pullback_diagram.to_category]; { refl <|> exact hgpx }⟩,
    rfl⟩ }

end category_theory
