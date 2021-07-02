--import topology.algebra.module
--import analysis.normed_space.finite_dimension
--import order.filter.basic

--open function
--open filter


/- Note:  hopefully all useful material has now been extracted from this file, so it can be
disregarded. -/

-- section
-- variables (k U V W: Type*)  [field k] [topological_space k]
-- [topological_space U] [topological_space V] [topological_space W]
--  [add_comm_group U] [add_comm_group V]
-- [add_comm_group W] [module k U] [module k V] [module k W]
-- [has_continuous_add U]
-- [has_continuous_add V]
-- [has_continuous_add W]
--  [has_continuous_smul k U]
-- (f : continuous_linear_map k U V) (g : continuous_linear_map k U W)


-- -- make this a general linear algebra theorem, no topology
-- theorem thm3 {A B C : Type*} (f : A → B) (g : A → C ) (p : C ) (h : injective (λ x, (f x, g x))) :
-- injective (f ∘ (coe: (g ⁻¹' {p}) → A ))
-- :=
-- begin
--   intros x y hf,
--   simp at hf,
--   have x2 := x.2,
--   have : g x = g y,
--   {
--     have := set.mem_preimage.mp (subtype.mem x),
--     have gxp := set.eq_of_mem_singleton this,
--     have := set.mem_preimage.mp (subtype.mem y),
--     have gyp := set.eq_of_mem_singleton this,
--     simp [gxp, gyp],
--   },
--   have : (f x, g x ) = (f y , g y),
--   {
--     simp [hf, this],
--   },
--   have := h this,
--   exact subtype.ext (h (congr_arg (λ (x : A), (f x, g x)) this)),
-- end


-- --make this a general linear algebra theorem, no topology
-- def thm5 {A B C : Type*}
-- (F : equiv A (B×C)) (p : C ):
-- equiv ((prod.snd ∘ F) ⁻¹' {p}) B :=  --(F.fst ∘ (coe: ((snd∘ F) ⁻¹' {p}) → A ))
-- { to_fun :=  λ x, prod.fst (F x),
--   inv_fun :=  λ b,  ⟨ F.symm (b, p), by simp⟩,
--   left_inv := _,
--   right_inv := _ }


-- -- make this a general linear algebra theorem, no topology
-- def thm4 {A B C : Type*} [topological_space A] [topological_space B] [topological_space C]
-- (F : homeomorph A (B×C)) (p : C ):
-- homeomorph ((prod.snd ∘ F) ⁻¹' {p}) B :=  --(F.fst ∘ (coe: ((snd∘ F) ⁻¹' {p}) → A ))
-- { to_fun :=  λ x, prod.fst (F x) ,
--   inv_fun := λ b,  ⟨ F.symm (b, p), by simp⟩ ,
--   left_inv :=
--   begin
--     rw left_inverse,
--     intros x,
--     have x1 := x.1,
--     have x2 := x.2,
--     have := F.left_inv x,

--   end,
--   right_inv := _,
--   continuous_to_fun := _,
--   continuous_inv_fun := _ }


-- theorem thm2 (p : W) (h₁ : injective (continuous_linear_map.prod f g))
-- (h₂ : is_open_map (f∘(coe : (g ⁻¹' {p}) → U))) :
-- open_embedding (f∘(coe : (g ⁻¹' {p}) → U)) :=
-- begin
--   apply open_embedding_of_continuous_injective_open,
--   -- (continuous_linear_map.continuous f),
--   exact continuous.comp (continuous_linear_map.continuous f) continuous_subtype_coe,
--   --have:= injective.comp,
--   exact thm3 f g p h₁,
--   exact h₂,
-- end

-- -- Heather homework
-- theorem thm1 (p : W) (h₁ : embedding (continuous_linear_map.prod f g))
-- (h₂ : is_open_map (f∘(coe : (g ⁻¹' {p}) → U))) :
-- tendsto (f∘(coe : (g ⁻¹' {p}) → U)) (cocompact _) (cocompact _) :=
-- begin
--   sorry,
-- end



-- theorem thm0 {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E]
-- [normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E]
-- {F : Type*} [normed_group F]
-- [normed_space 𝕜 F] [finite_dimensional 𝕜 F]
-- (f : linear_map 𝕜 E F) (h: surjective f)
--  :
-- is_open_map f :=
-- begin
--   have f_cont := linear_map.continuous_of_finite_dimensional f,

--   sorry,
-- end

--end



-- ********* HM new idea!!!



-- -- Natural bijection from the fibre over `p : C`, in a product type `B × C`, to `B`.
-- def fibre_embed {B C : Type*} (p : C) :
--   equiv (prod.snd ⁻¹' {p} : set (B × C)) B :=
-- { to_fun := prod.fst ∘ (coe : _ → B × C),
--   inv_fun := _,
--   left_inv := _,
--   right_inv := _ }

-- -- Natural homeomorphism from the fibre over `p : C`, in a product space `B × C`, to `B`.
-- def fibre_embed_homeomorph {B C : Type*} [topological_space B] [topological_space C] (p : C) :
--   homeomorph (prod.snd ⁻¹' {p} : set (B × C)) B :=
-- { continuous_to_fun := _,
--   continuous_inv_fun := _,
--   .. fibre_embed p }


-- /-- If the composition of a continuous function `f` with a closed embedding `g` is a closed
-- embedding, then `f` is a closed embedding -/
-- -- for `topology.maps`
-- lemma closed_embedding_of_closed_embedding_compose {A X Y : Type*} [topological_space A]
--   [topological_space X] [topological_space Y]
--   {f : A → X} {g : X → Y} (hf : continuous f) (hg : closed_embedding g)
--   (hfg : closed_embedding (g ∘ f)) :
--   closed_embedding f :=
-- begin
--   refine ⟨embedding_of_embedding_compose hf hg.continuous hfg.to_embedding, _⟩,
--   simpa [hg.closed_iff_image_closed, set.range_comp g f] using hfg.closed_range
-- end

-- /-- Given a closed embedding, the codomain-restriction to any closed subset is also a closed
-- embedding -/
-- -- for `topology.constructions`
-- lemma closed_embedding.cod_restrict {B X : Type*} [topological_space B]
--   [topological_space X]
--   {F : B → X} (hF : closed_embedding F) {s : set X} (hs : is_closed s) (hgs : ∀ x, F x ∈ s) :
--   closed_embedding (set.cod_restrict F s hgs) :=
-- begin
--   refine closed_embedding_of_closed_embedding_compose _ (closed_embedding_subtype_coe hs) hF,
--   exact continuous_subtype_mk _ hF.continuous
-- end

-- variables {k U V : Type*} [nondiscrete_normed_field k] [complete_space k]
--   [normed_group U] [normed_group V] [normed_space k U] [normed_space k V]
--   {f : linear_map k U V}

-- -- for `analysis.normed_space.finite_dimension`
-- /-- An injective linear map with finite-dimensional domain is a closed embedding. -/
-- lemma linear_equiv.closed_embedding_of_injective (hf : f.ker = ⊥) [finite_dimensional k U] :
--   closed_embedding ⇑f :=
-- let g := linear_equiv.of_injective f hf in
-- { closed_range := begin
--     haveI := f.finite_dimensional_range,
--     simpa [f.range_coe] using f.range.closed_of_finite_dimensional
--   end,
--   .. embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding }

-- variables {W : Type*} [normed_group W] [normed_space k W] {g : linear_map k U W}

-- /-- Here's how to do the big theorem, although this is a bit too specific to actually join the library -/
-- theorem big_thm [finite_dimensional k U] (p : W) (h₁ : (f.prod g).ker = ⊥) :
--   tendsto (f ∘ (coe : (g ⁻¹' {p}) → U)) (cocompact _) (cocompact _) :=
-- begin
--   let hf := linear_equiv.closed_embedding_of_injective h₁,
--   let hs : is_closed (prod.snd ⁻¹' {p} : set (V × W)) := is_closed_singleton.preimage continuous_snd,
--   have := (hf.comp (closed_embedding_subtype_coe (hs.preimage hf.continuous))).cod_restrict hs (by simp),
--   exact ((fibre_embed_homeomorph p).closed_embedding.comp this).tendsto_cocompact,
-- end


-- @[simp]
-- lemma coeff_coe {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)).val i j = ((g.val i j) : ℝ) := by refl

-- @[simp]
-- lemma coeff_coe' {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)) i j = ((g i j) : ℝ) := by refl

-- lemma div_eq_mul_conj_div_norm_sq {z w : ℂ} : z / w = (z * (w.conj)) / complex.norm_sq w :=
-- begin
--   rw [div_eq_mul_inv, inv_def, div_eq_mul_inv, mul_assoc],
--   norm_num,
-- end


-- @[simp]
-- lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by simp




-- lemma e14 : at_top ≤ cocompact ℝ :=
-- begin
--   intros s hs,
--   simp only [mem_at_top_sets],
--   simp only [mem_cocompact] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ := e7 ht.bounded,
--   use r + 1,
--   intros b hb,
--   apply hts,
--   intros hb',
--   have := hr _ hb',
--   simp only [real.norm_eq_abs, abs_le] at this,
--   linarith
-- end

-- lemma e16 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (s : set ℝ) :
--   norm ⁻¹' s ∈ cocompact E ↔ s ∈ (at_top : filter ℝ) :=
-- begin
--   rw [mem_at_top_sets, mem_cocompact],
--   split,
--   { rintros ⟨t, ht, hts⟩,
--     obtain ⟨r, hr⟩ := e7 ht.bounded,
--     use r + 1,
--     intros b hb,
--     obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
--     have h_norm : ∥b • (∥x∥)⁻¹ • x∥ = b := sorry,
--     have : b • (∥x∥)⁻¹ • x ∈ tᶜ,
--     { have := mt (hr (b • (∥x∥)⁻¹ • x)),
--       apply this,
--       linarith },
--     simpa [h_norm] using hts this },
--   { rintros ⟨r, hr⟩,
--     refine ⟨metric.closed_ball 0 r, proper_space.compact_ball 0 r, _⟩,
--     intros x hx,
--     simp at hx,
--     exact hr (∥x∥) hx.le },
-- end

-- lemma e17 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] :
--   map norm (cocompact E) = (at_top : filter ℝ) :=
-- begin
--   ext s,
--   exact e16 s
-- end

-- lemma e15 {α : Type*} {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (l : filter α) {f : α → E} :
--   tendsto f l (cocompact E) ↔ tendsto (norm ∘ f) l at_top :=
-- begin
--   split,
--   { exact tendsto_norm_cocompact_at_top.comp },
--   sorry
-- end


-- lemma finite_integers {M : ℝ} :
--   set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
-- begin
--     let s:= finset.Ico_ℤ (⌊-M⌋) (⌊M⌋+1),
--     suffices : {c : ℤ | |↑c| ≤ M} ⊆  s,
--     {
--       refine set.finite.subset s.finite_to_set this,
--     },
--     intros c,
--     simp [s],
--     intros h,
--     rw abs_le at h,
--     have h1 := h.1,
--     have h2 := h.2,
--     split,
--     {
--       have : (⌊-M⌋ :ℝ ) ≤ -M :=  floor_le (-M),
--       have := le_trans this h1,
--       exact_mod_cast this,
--     },
--     {
--       have : (c:ℝ ) < (⌊M⌋:ℝ) + 1,
--       {
--         calc
--         (c:ℝ) ≤ M           : h2
--         ...   < (⌊M⌋:ℝ) + 1 : M_lt_Mp1 M,
--       },

--       norm_cast at this,
--       exact this,
--     },
-- end

-- -- for `normed_space.basic`
-- lemma metric.bounded.exists_norm_le {α : Type*} [normed_group α] {s : set α} (hs : metric.bounded s) :
--   ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
-- begin
--   rcases s.eq_empty_or_nonempty with (rfl | hs'),
--   { simp },
--   obtain ⟨R₁, hR₁⟩ := hs,
--   obtain ⟨x, hx⟩ := hs',
--   use ∥x∥ + R₁,
--   intros y hy,
--   have : ∥x - y∥ ≤ R₁ := by simpa [dist_eq_norm] using hR₁ x y hx hy,
--   have := norm_le_insert x y,
--   linarith
-- end

-- -- for `order.filter.basic`
-- lemma e9 {α : Type*} (l : filter α) {s t : set α} (hst : s ∪ tᶜ ∈ l) (ht : t ∈ l) : s ∈ l :=
-- begin
--   refine mem_sets_of_superset _ (s.inter_subset_left t),
--   convert inter_mem_sets hst ht using 1,
--   ext,
--   simp only [set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
--   finish
-- end


-- lemma e10 {α : Type*} {l : filter α} {E F : Type*} [normed_group E] [normed_group F] [proper_space E]
--   {f : α → E} {g : α → F} (h : asymptotics.is_O f g l) (hf : tendsto f l (cocompact E)) :
--   tendsto g l (cocompact F) :=
-- begin
--   rw tendsto_def at ⊢ hf,
--   intros s hs,
--   simp [filter.mem_cocompact'] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ sᶜ, ∥p∥ ≤ r := (ht.bounded.subset hts).exists_norm_le,
--   rw asymptotics.is_O_iff at h,
--   obtain ⟨c, hc⟩ := h,
--   rw eventually_iff_exists_mem at hc,
--   obtain ⟨v, hv, hvfg⟩ := hc,
--   have : ∀ x ∈ v ∩ g ⁻¹' sᶜ, x ∈ f ⁻¹' metric.closed_ball (0:E) (c * r),
--   { rintros x ⟨hxv, hxgs⟩,
--     have := hr (g x) hxgs,
--     have := hvfg x hxv,
--     simp,
--     sorry },
--   have h₂ : f ⁻¹' (metric.closed_ball (0:E) (c * r))ᶜ ⊆ g ⁻¹' s ∪ vᶜ,
--   { intros x,
--     have := this x,
--     simp only [set.mem_preimage, set.mem_inter_eq, set.mem_compl_eq] at this,
--     simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq],
--     contrapose!,
--     finish },
--   have h₃ : f ⁻¹' (metric.closed_ball 0 (c * r))ᶜ ∈ l,
--   { apply hf (metric.closed_ball (0:E) (c * r))ᶜ,
--     simp only [mem_cocompact'],
--     refine ⟨metric.closed_ball (0:E) (c * r), proper_space.compact_ball 0 (c * r), _⟩,
--     simp },
--   have : g ⁻¹' s ∪ vᶜ ∈ l := mem_sets_of_superset h₃ h₂,
--   refine e9 l this hv
-- end


-- lemma tendsto_cocompact_of_antilipschitz {α β : Type*} [metric_space α] [proper_space α]
--   [metric_space β] {c : nnreal} {f : α → β} (hf : antilipschitz_with c f) :
--   tendsto f (cocompact α) (cocompact β) :=
-- begin
--   rw tendsto_iff_eventually,
--   simp only [mem_cocompact, eventually_iff_exists_mem],
--   rintros p ⟨v, hv, hvp⟩,
--   rw mem_cocompact' at hv,
--   obtain ⟨t, ht, htv⟩ := hv,
--   obtain ⟨r, hr⟩ := ht.bounded,
--   -- have := hf.bounded_preimage ht.bounded,
--   by_cases h : ∃ x, ¬ p (f x),
--   { obtain ⟨x, hx⟩ := h,
--     have hxt : f x ∈ t := htv (mt (hvp (f x)) hx),
--     refine ⟨(metric.closed_ball x (c * r))ᶜ, _, _⟩,
--     { rw mem_cocompact,
--       refine ⟨metric.closed_ball x (c * r), proper_space.compact_ball x (↑c * r), rfl.subset⟩ },
--     intros x' hx',
--     have hxx'r : r < dist (f x) (f x'),
--     { simp at hx',
--       rw dist_comm at hx',
--       rw antilipschitz_with_iff_le_mul_dist at hf,
--       have : dist x x' ≤ c * dist (f x) (f x') := hf x x',
--       have := lt_of_lt_of_le hx' this,
--       sorry }, -- this follows from the previous line except with a special case for `c = 0`
--     have := mt (hr (f x) (f x') hxt),
--     push_neg at this,
--     have := (mt (@htv (f x'))) (this hxx'r),
--     apply hvp,
--     simpa using this },
--   { push_neg at h,
--     refine ⟨set.univ, univ_mem_sets, _⟩,
--     intros x hx,
--     exact h x },
-- end

-- lemma tendsto_at_top_sum_sq :
--   tendsto (λ x : ℝ × ℝ, x.1 ^ 2 + x.2 ^ 2) (cocompact (ℝ × ℝ)) at_top :=
-- begin
--   refine tendsto_at_top_mono _
--     (tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top),
--   rintros ⟨x₁, x₂⟩,
--   simp only [prod.norm_def, real.norm_eq_abs],
--   cases max_choice (|x₁|) (|x₂|) with h h;
--   { rw [h, abs_mul_abs_self],
--     nlinarith },
-- end

-- @[simp] lemma expand_sum_01 {R : Type*} [ring R] (f : fin 2 → R ) :
-- (∑ (x : fin 2), f x) = f 0 + f 1 :=
-- by simp [fin.sum_univ_succ]


-- -- method 1 -
-- def line (cd : coprime_ints) : set (matrix (fin 2) (fin 2) ℝ) :=
--   {g | g 1 0 = (cd : ℤ × ℤ).1 ∧ g 1 1 = (cd : ℤ × ℤ).2 ∧ det g = 1}

-- - Do we need this? Maybe delete
-- lemma line_proper (cd : coprime_ints) :
--   map coe (cocompact (line cd)) = cocompact (matrix (fin 2) (fin 2) ℝ) :=
-- begin

--   sorry
-- end
-- -


-- -- make `line` an affine subspace of 2x2 matrices, using the following lemma
-- lemma line_det (cd : coprime_ints) {g : matrix _ _ ℝ} (hg : g ∈ line cd) :
--   g 0 0 * cd.d - g 0 1 * cd.c = 1 :=
-- begin
--   convert hg.2.2,
--   rw [det2, hg.1, hg.2.1],
--   ring,
-- end

-- lemma in_line (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
--   ↑(g : SL(2, ℝ)) ∈ line cd :=
-- begin
--   rw line,
--   rw set.mem_set_of_eq,
--   rw bottom_row at hg,
--   simp only [subtype.val_eq_coe] at hg,
--   split,
--   simp [hg],
--   sorry,
--   split,
--   simp [hg],
--   sorry,
--   exact (g: SL(2,ℝ)).2,
-- end

-- def to_line (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line cd :=
-- ⟨↑(g : SL(2, ℝ)), in_line cd g.2⟩




-- lemma sddsf (cd : coprime_ints) (z : ℂ) :
--   tendsto (λ g : lattice_intersect (line cd), _root_.abs (smul_aux' ↑(lattice_intersect_fun _ g) z).re)
--     cofinite at_top :=
-- (tendsto_at_top_abs.comp (tendsto_action cd z)).comp (tendsto_lattice_intersect_fun (line cd))

-- -- method 2 -
-- def line' (cd : coprime_ints) : set (ℝ × ℝ) :=
--   {ab | ab.1 * (cd : ℤ × ℤ).2 - ab.2 * (cd : ℤ × ℤ).1 = 1}

-- def in_line' (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
--   (↑(g 0 0), ↑(g 0 1)) ∈ line' cd :=
-- sorry

-- def to_line' (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line' cd :=
-- ⟨(g 0 0, g 0 1), in_line' cd g.2⟩

-- lemma tendsto_line' (cd : coprime_ints) : tendsto (to_line' cd) cofinite (cocompact _) := sorry

-- lemma inv_image_eq_line (cd : coprime_ints) :
--   bottom_row ⁻¹' {cd} = (prod.map coe coe : ℤ × ℤ → ℝ × ℝ) ⁻¹' line cd :=
-- sorry

-- end




-- lemma tendsto_acbd (cd : coprime_ints):
--   tendsto (λ g, acbd (↑g)) (cocompact (line cd)) (cocompact ℝ) :=
-- begin
--   let cabs := _root_.abs cd.c,
--   let dabs := _root_.abs cd.d,
--   let maxCD := max cabs dabs,
--   intros K hK ,
--   rw mem_cocompact at hK,

--   obtain ⟨ K1, hK1, hK2⟩  := hK,

--   obtain ⟨ t, ht⟩  := (metric.bounded_iff_subset_ball 0).mp (is_compact.bounded hK1),
--   rw mem_map,
--   rw mem_cocompact,
--   refine ⟨
--   ((coe : line cd → (matrix (fin 2) (fin 2) ℝ)) ⁻¹'
--    (metric.closed_ball (0: matrix (fin 2) (fin 2) ℝ) (max (2*(_root_.abs t)+1) maxCD) )),
--    sorry, _⟩ ,
--    --simp,
--   rw set.compl_subset_comm,
--   rw set.compl_subset_comm at hK2,
--   intros g hg,
--   simp [dist_eq_norm] at hg,
--   simp only [set.mem_preimage, metric.mem_closed_ball,  int_cast_abs, subtype.val_eq_coe],
--   have : acbd ↑g ∈ metric.closed_ball (0:ℝ) t,
--   {
--     apply ht,
--     apply hK2,
--     exact hg,
--   },
--   rw dist_pi_def,
--   let a : nnreal := nnreal.of_real (max (2 * |t| + 1) ↑maxCD),
--   rw ← nnreal.coe_of_real (max (2 * |t| + 1) ↑maxCD),
--   norm_cast,
--   have : (∀ (b : fin 2), b ∈ finset.univ → (λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) 0) b ≤ a) := sorry,
--   refine @finset.sup_le nnreal (fin 2) _ (finset.univ) ((λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) (0))) a _,

--   sorry
-- end

-- - Is this non-crap? (More elegant phrasing?...) We know that $ℤ$ matrices are discrete in $ℝ$; so intersection of $Z$ matrices is discrete in line -
-- lemma tendsto_inverse_image_fun' {α β : Type*} [topological_space β] (A : set α) (B : set β)
--   {f : α → β} (hf₁ : ∀ x ∈ A, f x ∈ B ) (hf₂ : tendsto f cofinite (cocompact _)) :
--   tendsto (subtype.map f (λ x h, set.mem_def.mp (hf₁ x h))) cofinite (cocompact _) :=
-- begin
-- --  refine tendsto_inverse_image_fun subtype.coe_injective continuous_subtype_coe _ hf₂,
--   refine filter.tendsto.of_tendsto_comp _ (comap_cocompact continuous_subtype_coe),
--   simpa [hf₁] using hf₂.comp subtype.coe_injective.tendsto_cofinite,
-- end


-- -- Big filter theorem -
-- theorem big_thm' (cd : coprime_ints) (w : ℝ) :
--   tendsto (λ A : bottom_row ⁻¹' {cd}, acbd cd ↑A + w) cofinite (cocompact ℝ) :=
-- begin
--   let cd' : fin 2 → ℤ :=  λ i, if i = 0 then cd.c else cd.d,
--   let l := bottom_row ⁻¹' {cd},
--   let f : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ := λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
--   have hf : tendsto f cofinite (cocompact _) :=
--     cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
--   have hl : ∀ g ∈ l, f g ∈ new_line_def cd,
--   { intros g hg,
--     simp [new_line_def, line_map, matrix.coord, f],
--     split,
--     { norm_cast,
--       convert g.det_coe_matrix using 1,
--       sorry },
--     { sorry } },
--   let f' : l → new_line_def cd := subtype.map f hl,
--   have h₁ : tendsto f' cofinite (cocompact _),
--   { refine filter.tendsto.of_tendsto_comp _ (comap_cocompact continuous_subtype_coe),
--     simpa [hl] using hf.comp subtype.coe_injective.tendsto_cofinite },
--   have h₂ : tendsto (λ A, acbd cd ↑A + w) (cocompact (new_line_def cd)) (cocompact ℝ),
--   { let hf := linear_equiv.closed_embedding_of_injective (lin_indep_acbd cd),
--     let p : ℝ × (fin 2 → ℝ) := (1, λ i, if i = 0 then cd.c else cd.d),
--     let hs : is_closed (prod.snd ⁻¹' {p} : set (ℝ × (ℝ × (fin 2 → ℝ)))) :=
--       is_closed_singleton.preimage continuous_snd,
--     have := (hf.comp (closed_embedding_subtype_coe (hs.preimage hf.continuous))).cod_restrict hs (by simp),
--     have := ((fibre_embed_homeomorph p).trans (homeomorph.add_right w)).closed_embedding.comp this,
--     exact this.tendsto_cocompact },
--   have := h₂.comp h₁,
--   convert this,
-- end




-- example : T⁻¹ * T = 1 := inv_mul_self T

-- example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

-- example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

-- example { x y : SL(2,ℤ)} (ℍ : x.1 = y.1) : x = y := subtype.eq h

-- @[simp]
-- lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

-- @[simp]
-- lemma mat_ext_iff  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
--   x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
-- begin
--   rw ←matrix.ext_iff,
--   split,
--   {
--     intro h,
--     rw h,
--     tauto },
--   {
--     rintros ⟨h1, h2, h3, h4⟩ i j,
--     fin_cases i; fin_cases j; assumption,
--   }
-- end

-- @[simp]
-- lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
--   = (1 : matrix (fin 2) (fin 2) F) := by {simp}


-- lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
-- begin
--   suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
--   { exact inv_eq_of_mul_eq_one this},
--   simp [T],
-- end

-- lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

-- lemma T_pow_ℕ {n : ℕ} : T ^ n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   induction n with n hn,
--   { simp },
--   { rw [pow_succ', hn, T],
--     simp [add_comm] }
-- end

-- lemma T_inv_pow_ℕ {n : ℕ} : (T⁻¹)^n = { val := ![![1, -n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   induction n with n hn,
--   simp,
--   have : (T⁻¹) ^ n.succ = ((T⁻¹)^n)* (T⁻¹),
--   {
--     exact pow_succ' (T⁻¹) n,
--   },
--   rw this,
--   rw hn,
--   rw T_inv,
--   simp,
-- end


-- lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   by_cases n_ge_0 : 0 ≤ n,
--   lift n to ℕ with n_ge_0,
--   refine T_pow_ℕ,
--   exact n_ge_0,
--   have : T ^ n = T ^ (- (-n)) := by simp,
--   rw this,
--   rw T_n_def,
--   generalize' hk : -n=k,
--   have k_ge_0 : 0 ≤ k,
--   {
--     rw ← hk,
--     linarith,
--   },
--   have : n = -k,
--   {
--     rw ← hk,
--     ring,
--   },
--   rw this,
--   lift k to ℕ using k_ge_0,
--   rw gpow_coe_nat,
--   norm_cast,
--   rw T_inv_pow_ℕ,
-- end

-- lemma T_action {z : ℍ} : (T • z).1 = z + 1 :=
-- begin
--   convert @smul_sound T z,
--   simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
--   simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
-- end


-- lemma Tn_action {z : ℍ} {n : ℤ} : (T^n • z).1 = z + n :=
-- begin
--   have := @smul_sound (T^n) z,
--   convert this,
--   rw smul_aux,
--   rw T_pow,
--   rw top,
--   rw bottom,
--   simp,
-- end

-- lemma S_action (z : ℍ) : (S • z).1 = -z⁻¹ :=
-- begin
--   convert @smul_sound S z,
--   simp only [smul_aux_def, top, bottom, S, has_coe_SL_apply, subtype.coe_mk, map_cons],
--   simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
--   ring,
-- end

-- lemma S_bottom (z : ℍ) : bottom S z = (z:ℂ) :=
--   by simp [S, bottom, map_cons, comp_cons, cons_apply_one, cons_apply_zero]



-- lemma S_action_im (z : ℍ) : (S • z).im = z.im / norm_sq z :=
-- begin
--   rw matrix.special_linear_group.im_smul_int,
--   field_simp [normsq_bottom_ne_zero, norm_sq_nonzero, S, bottom, map_cons, comp_cons,
--     cons_apply_one, cons_apply_zero],
-- end

-- lemma T'_action_re (z : ℍ) : (T' • z).re = z.re - 1 :=
-- begin
--   simp [T', smul_aux, smul_aux', top, bottom, map_cons, comp_cons, cons_apply_one, cons_apply_zero],
--   refl,
-- end

-- lemma T_action_re (z : ℍ) : (T • z).re = z.re + 1 :=
-- begin
-- end




-- lemma half_ge_x_T_inv (z : ℍ) (h : 1/2 < z.re) : |(T' • z).re| < |z.re| :=
-- begin
--   have : |z.re - 1| < |z.re|,
--   { rw [(abs_eq_self.mpr (by linarith : 0 ≤ z.re)), abs_lt],
--     split; linarith, },
--   convert this,
--   simp [T', smul_aux, smul_aux', top, bottom, map_cons, comp_cons, cons_apply_one, cons_apply_zero],
--   refl,
-- end

-- lemma half_le_neg_x_T (z : ℍ) (h : 1/2 < - z.re) : |(T • z).re| < |z.re| :=
-- begin
--   have : |z.re + 1| < |z.re|,
--   { rw [(abs_eq_neg_self.mpr (by linarith : z.re ≤ 0)), abs_lt],
--     split; linarith, },
--   convert this,
--   simp [T, smul_aux, smul_aux', top, bottom, map_cons, comp_cons, cons_apply_one, cons_apply_zero],
--   refl,
-- end

-- lemma norm_sq_ge_one_of_act_S {z : ℍ} (h : (S • z).im ≤ z.im) : 1 ≤ norm_sq z :=
-- begin
--   by_contradiction hcontra,
--   push_neg at hcontra,
--   have := im_lt_im_S hcontra,
--   linarith,
-- end



-- lemma T_inv_action {z : ℍ} : (T⁻¹ • z).1 = z - 1 :=
-- begin
--   convert @smul_sound (T⁻¹) z,
--   rw smul_aux,
--   rw T_inv,
--   simp,
--   ring,
-- end

------------------------------------

-- lemma find_g_with_min_re (z:ℍ) (cd : coprime_ints) :
-- ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ),  bottom_row g = bottom_row g' →
-- _root_.abs ((g • z).val.re) ≤ _root_.abs ((g' • z).val.re)) :=
-- begin
-- -  -- Argh this is all wrong;
-- -- Need to look somehow at the set of all preimages of cd
-- -- among those, choose g with minimal real part
-- -- the rest is tautological
--   obtain ⟨g, hg⟩ := bottom_row_surj cd,
--   use g,
--   split,
--   exact hg,
--   intros g' hg',
--   by_contradiction hcontra,
--   push_neg at hcontra,
--   obtain ⟨n, hn⟩ := bot_row_eq_diff_by_T_n g g' hg',
--   rw hn at hcontra,
--   -
--   sorry,
-- end
