
-- { carrier := { a | localization.mk a 1 ∈
--     ideal.span { z : localization.away f | ∃ (c : q.1), z = c.1.1 } },
--   zero_mem' := begin
--     rw [set.mem_set_of_eq], apply ideal.subset_span,
--     use 0, rw localization.mk_zero, refl,
--   end,
--   add_mem' := λ a b ha hb, begin
--     rw [set.mem_set_of_eq] at ha hb ⊢,
--     have eq1 : localization.mk (a + b) 1 = localization.mk a 1 + localization.mk b 1,
--     { rw localization.add_mk, rw [←subtype.val_eq_coe],
--       have : (1 : submonoid.powers f).val = 1 := rfl,
--       erw [this, one_mul, mul_one],
--       congr' 1, rw [add_comm], congr,
--       convert (one_mul _).symm,  },
--     erw eq1, apply submodule.add_mem _ ha hb,
--   end,
--   smul_mem' := λ a b hb, begin
--     rw [set.mem_set_of_eq] at hb ⊢,
--     rw smul_eq_mul,
--     have eq1 : (localization.mk (a * b) 1 : localization.away f) =
--       localization.mk a 1 * localization.mk b 1,
--     { rw localization.mk_mul,
--       congr' 1, erw one_mul, },
--     erw eq1,
--     refine ideal.mul_mem_left (ideal.span {z : localization.away f | ∃ (c : q.val), z = c.1.1})
--       (localization.mk a 1) hb,
--   end }





      -- have mem1 : ∃ (g : degree_zero_part _ f m f_deg), z ∈ prime_spectrum.basic_open g,
      -- {
      --   obtain ⟨v, hv1, hv2, hv3⟩ := is_topological_basis.exists_subset_of_mem_open
      --     (prime_spectrum.is_topological_basis_basic_opens) (set.mem_univ _) (is_open_univ),
      --   erw set.mem_range at hv1,
      --   obtain ⟨g, rfl⟩ := hv1,
      --   refine ⟨g, hv2⟩, },

      -- obtain ⟨g, hg⟩ := mem1,
      -- refine ⟨(prime_spectrum.basic_open g).1, _, (prime_spectrum.basic_open g).2, hg⟩,
      -- have set_eq2 : isos.top_component.forward.to_fun 𝒜 f m f_deg '' {x | x.val ∈
      --   (projective_spectrum.basic_open 𝒜 f).val ⊓ (projective_spectrum.basic_open 𝒜 a).val }
      -- = isos.top_component.forward.to_fun 𝒜 f m f_deg '' {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 f).1}
      -- ⊓ isos.top_component.forward.to_fun 𝒜 f m f_deg '' {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 a).1},
      -- { erw ←set.image_inter,
      --   congr' 1,
      --   refine isos.top_component.forward.to_fun_inj _ _ _ hm _, },
      -- erw set_eq2,
      -- rcases g with ⟨g, g_degree_zero⟩,
      -- change ∃ _, _ at g_degree_zero,
      -- obtain ⟨k, β, β_mem, rfl⟩ := g_degree_zero,
      -- dsimp only,

      -- have set_eq3 : isos.top_component.forward.to_fun 𝒜 f m f_deg ''
      --   ({x | x.1 ∈ (projective_spectrum.basic_open 𝒜 β) ⊓ (projective_spectrum.basic_open 𝒜 f)}) =
      --   (prime_spectrum.basic_open (⟨localization.mk β ⟨f^k, ⟨k, rfl⟩⟩, ⟨k, β, β_mem, rfl⟩⟩
      --     : degree_zero_part 𝒜 f m f_deg)).1 := sorry,

      -- erw ←set_eq3,
      -- apply set.image_subset,
      -- { intros γ hγ,
      --   change γ.val ∈ _ at hγ,
      --   change γ.val ∈ _,
      --   refine ⟨hγ.2, _⟩,
      --   sorry },
      -- apply set.subset_inter,
      -- { intros γ hγ,
      --   erw set.mem_image,
      --   refine ⟨isos.top_component.backward.to_fun 𝒜 f m hm f_deg γ, _,
      --     -- isos.top_component.forward_backward 𝒜 f m hm f_deg γ
      --     -- too slow to compile
      --     sorry⟩,
      --   { sorry, -- too slow to compile
      --     -- change (isos.top_component.backward.to_fun 𝒜 f m hm f_deg γ).val ∈ _,
      --     -- erw projective_spectrum.mem_basic_open,
      --     -- unfold isos.top_component.backward.to_fun,
      --     -- dsimp only,
      --     -- intro rid,

      --     -- change f ∈ isos.backward.carrier.as_ideal 𝒜 f m hm f_deg γ at rid,
      --     -- change f ∈ isos.backward.carrier 𝒜 f m hm f_deg γ at rid,
      --     -- change ∀ (i : ℕ), _ at rid,
      --     -- specialize rid m,
      --     -- simp only [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same 𝒜 f_deg] at rid,
      --     -- apply γ.is_prime.ne_top,
      --     -- rw ideal.eq_top_iff_one,
      --     -- convert rid,
      --     -- rw [subtype.ext_iff_val, show (1 : degree_zero_part 𝒜 f m f_deg).val = 1, from rfl],
      --     -- dsimp only,
      --     -- symmetry,
      --     -- convert localization.mk_self _,
      --     -- rw [←subtype.val_eq_coe],
      --   },

      -- },


      -- { intros γ hγ,
      --   refine ⟨isos.top_component.backward.to_fun 𝒜 f m hm f_deg γ, _,
      --     -- isos.top_component.forward_backward 𝒜 f m hm f_deg γ
      --     -- too slow to compile
      --     sorry⟩,
      --   change (isos.top_component.backward.to_fun 𝒜 f m hm f_deg γ).val ∈ _,
      --   erw projective_spectrum.mem_basic_open,
      --   unfold isos.top_component.backward.to_fun,
      --   dsimp only,
      --   intro rid,

      --   change a ∈ isos.backward.carrier.as_ideal 𝒜 f m hm f_deg γ at rid,
      --   change a ∈ isos.backward.carrier 𝒜 f m hm f_deg γ at rid,
      --   change ∀ (i : ℕ), _ at rid,
      --   rcases hz with ⟨z, z_mem, rfl⟩,
      --   sorry },
