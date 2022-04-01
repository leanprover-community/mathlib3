-- import tactic.coherence

-- open category_theory

-- namespace tactic

-- namespace bicategory
-- open_locale bicategory
-- open category_theory.bicategory

-- /-- normalize 1-morphisms -/
-- meta def normalize : expr → expr → tactic expr
-- | p `(%%f ≫ %%g) := do pf ← normalize p f, normalize pf g
-- | p `(𝟙 %%a)      := return p
-- | p f              := to_expr ``(%%p ≫ %%f)

-- meta def to_normalize_aux : expr → expr → tactic expr
-- | p `(%%f ≫ %%g) := do
--     pf₂  ← to_normalize_aux p f,
--     pf   ← normalize p f,
--     pfg₂ ← to_normalize_aux pf g,
--     to_expr ``((α_ %%p %%f %%g).symm ≪≫ whisker_right_iso %%pf₂ %%g ≪≫ %%pfg₂)
-- | p `(𝟙 %%a)     := to_expr ``(ρ_ %%p)
-- | p f             := to_expr ``(iso.refl (%%p ≫ %%f))

-- /-- 2-isomorphism between the original 1-morphism and the normalized 1-morphism -/
-- meta def to_normalize (f : expr) : tactic expr :=
-- do
--   `(%%a ⟶ %%b) ← infer_type f,
--   p  ← to_expr ``(𝟙 %%a),
--   f' ← to_normalize_aux p f,
--   to_expr ``((λ_ _).symm ≪≫ %%f')


-- /-- 2-isomorphism between `f` and `g` that are related by `id_comp`, `comp_id`, and `assoc`. -/
-- meta def can (f : expr) (g : expr) : tactic expr :=
-- do
--   `(%%a ⟶ %%b) ← infer_type f,
--   f' ← to_normalize f,
--   g' ← to_normalize g,
--   to_expr ``(%%f' ≪≫ iso.symm %%g')

-- set_option eqn_compiler.max_steps 5000

-- meta def is_coherent_hom : expr → bool
-- | `(%%η ≫ %%θ) := is_coherent_hom η ∧ is_coherent_hom θ
-- | `(%%f ◁ %%η)  := is_coherent_hom η
-- | `(%%η ▷ %%h)  := is_coherent_hom η
-- | `(iso.hom (α_ %%f %%g %%h)) := true
-- | `(iso.inv (α_ %%f %%g %%h)) := true
-- | `(iso.hom (λ_ %%f)) := true
-- | `(iso.inv (λ_ %%f)) := true
-- | `(iso.hom (ρ_ %%f)) := true
-- | `(iso.inv (ρ_ %%f)) := true
-- | `(𝟙 %%f)           := true
-- | _ := false

-- meta def coherent_reassoc : expr → expr → tactic expr
-- | `(%%η₁ ≫ %%η₂) `(%%η₃ ≫ %%η₄) := do
--   if is_coherent_hom η₂ then do
--     if is_coherent_hom η₃ then do
--       η₂₃₄ ← to_expr ``((%%η₂ ≫ %%η₃) ≫ %%η₄),
--       coherent_reassoc η₁ η₂₃₄
--     else do
--       η₂₃₄ ← to_expr ``(%%η₂ ≫ (%%η₃ ≫ %%η₄)),
--       coherent_reassoc η₁ η₂₃₄
--   else do
--     if is_coherent_hom η₃ then do
--       η₂₃₄ ← to_expr ``(𝟙 _ ≫ %%η₂ ≫ (%%η₃ ≫ %%η₄)),
--       coherent_reassoc η₁ η₂₃₄
--     else do
--       η₂₃₄ ← to_expr ``(𝟙 _ ≫ %%η₂ ≫ 𝟙 _ ≫ %%η₃ ≫ %%η₄),
--       coherent_reassoc η₁ η₂₃₄
-- | `(%%η₁ ≫ %%η₂) η₃ := do
--   if is_coherent_hom η₂ then do
--     η₂₃ ← to_expr ``(%%η₂ ≫ %%η₃),
--     coherent_reassoc η₁ η₂₃
--   else do
--     η₂₃ ← to_expr ``(𝟙 _ ≫ %%η₂ ≫ %%η₃),
--     coherent_reassoc η₁ η₂₃
-- | η₁ η₂ := do
--   if is_coherent_hom η₁ then
--     match η₂ with
--     | `(%%η₂' ≫ %%η₃') := to_expr ``((%%η₁ ≫ %%η₂') ≫ %%η₃')
--     | η₂ := to_expr ``(%%η₁ ≫ %%η₂)
--   end
--   else do
--     to_expr ``(𝟙 _ ≫ %%η₁ ≫ %%η₂)

-- meta def coherent_reassoc' (f : expr) : tactic expr := do
--   g ← to_expr ``(𝟙 _),
--   coherent_reassoc f g

-- end bicategory

-- namespace interactive
-- setup_tactic_parser

-- /--
-- The tactic `can` yields an isomorphism `f ≅ g` for 1-morphisms `f` and `g` that are
-- related by `id_comp`, `comp_id`, and `assoc`.
-- -/
-- meta def can_iso : tactic unit :=
-- do
--   `(%%f ≅ %%g) ← get_goal >>= infer_type,
--   f_to_g ← tactic.bicategory.can f g,
--   let s := simp_lemmas.mk,
--   s ← s.add_simp ``iso.trans_assoc,
--   s ← s.add_simp ``iso.refl_trans,
--   s ← s.add_simp ``iso.trans_refl,
--   (f_to_g', pr', _) ← simplify s [] f_to_g,
--   tactic.exact f_to_g'

-- meta def can_hom : tactic unit :=
-- do
--   `(%%f ⟶ %%g) ← get_goal >>= infer_type,
--   f_to_g ← tactic.bicategory.can f g,
--   f_to_g' ← to_expr ``(iso.hom %%f_to_g),
--   let s := simp_lemmas.mk,
--   s ← s.add_simp ``iso.trans_hom,
--   s ← s.add_simp ``iso.symm_hom,
--   s ← s.add_simp ``iso.refl_hom,
--   s ← s.add_simp ``iso.trans_inv,
--   s ← s.add_simp ``iso.symm_inv,
--   s ← s.add_simp ``iso.refl_inv,
--   s ← s.add_simp ``bicategory.whisker_right_iso_hom,
--   s ← s.add_simp ``bicategory.whisker_right_iso_inv,
--   s ← s.add_simp ``bicategory.id_whisker_right,
--   s ← s.add_simp ``category.assoc,
--   s ← s.add_simp ``category.id_comp,
--   s ← s.add_simp ``category.comp_id,
--   (f_to_g'', pr', _) ← simplify s [] f_to_g',
--   tactic.exact f_to_g''

-- meta def can : tactic unit :=
-- can_iso <|> can_hom

-- meta def assoc_simps : tactic unit :=
-- `[simp only [
--   category.assoc,
--   bicategory.comp_whisker_left,
--   bicategory.id_whisker_left,
--   bicategory.whisker_right_comp, bicategory.whisker_right_id,
--   bicategory.whisker_left_comp, bicategory.whisker_left_comp_assoc,
--   bicategory.whisker_left_id,
--   bicategory.comp_whisker_right, bicategory.comp_whisker_right_assoc,
--   bicategory.id_whisker_right,
--   bicategory.whisker_assoc]]

-- meta def coherent_reassoc : tactic unit :=
-- do
--   `[try { assoc_simps }],
--   `[try { simp only [←category.assoc] }],
--   (lhs, rhs) ← get_goal >>= infer_type >>= match_eq,
--   lhs' ← tactic.bicategory.coherent_reassoc' lhs,
--   rhs' ← tactic.bicategory.coherent_reassoc' rhs,
--   ln ← get_unused_name `lhs,
--   rn ← get_unused_name `rhs,
--   «have» ln ``(%%lhs = %%lhs') ``(by simp only [category.assoc, category.id_comp, category.comp_id]),
--   «have» rn ``(%%rhs = %%rhs') ``(by simp only [category.assoc, category.id_comp, category.comp_id]),
--   `[rw [lhs, rhs]],
--   `[clear lhs],
--   `[clear rhs]
-- --  `[repeat { congr' 1, try { coherence } }]
-- --  `[try { coherence }]

-- open_locale bicategory
-- universes w v u
-- variables {B : Type u} [bicategory.{w v} B]
-- variables {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)

-- example : (f ≫ g) ≫ h ≅ f ≫ (g ≫ h) := by can
-- example : ((f ≫ g) ≫ 𝟙 c ≫ h) ≫ i ≅ f ≫ (g ≫ h) ≫ i := by can
-- example : f ≫ g ≫ 𝟙 c ≫ h ≫ i ≫ 𝟙 e ≅ 𝟙 a ≫ (f ≫ g ≫ h) ≫ 𝟙 d ≫ i := by can
-- example : f ≅ f := by can

-- def assoc₄ : ((f ≫ g) ≫ h) ≫ i ≅ f ≫ g ≫ h ≫ i := by can

-- example {f₀ h₀ : a ⟶ e} (η : f₀ ⟶ ((f ≫ g) ≫ h) ≫ i)
-- (θ : f ≫ g ≫ h ≫ i ⟶ h₀) : η ≫ (by can) ≫ θ =
--   𝟙 _ ≫ η ≫ (α_ _ _ _).hom ≫ 𝟙 _ ≫ (α_ _ _ _).hom ≫ θ :=
-- begin
--   coherent_reassoc,
--   repeat { congr' 1, try { coherence } }
-- end

-- example : (by can : ((f ≫ g) ≫ h) ≫ i ⟶ f ≫ g ≫ h ≫ i) =
--   (α_ _ _ _).hom ≫ (α_ _ _ _).hom  :=
-- begin
--   coherent_reassoc,
--   repeat { congr' 1, try { coherence } }
-- end

-- example {f₀ h₀ : a ⟶ e} (η : f₀ ⟶ ((f ≫ g) ≫ h) ≫ i)
-- (θ : f ≫ g ≫ h ≫ i ⟶ h₀) : η ≫ (assoc₄ f g h i).hom ≫ θ =
--   η ≫ (α_ _ _ _).hom ≫ 𝟙 _ ≫ (α_ _ _ _).hom ≫ θ :=
-- begin
--   dunfold assoc₄,
--   dsimp,
--   coherent_reassoc,
--   repeat { congr' 1, try { coherence } }
-- end

-- example (f g : a ⟶ a) (η : f ⟶ g) (η' : g ⟶ 𝟙 a ≫ 𝟙 a) :
--   η ≫ η' ≫ (λ_ $ 𝟙 a).hom = (η ≫ η') ≫ (ρ_ $ 𝟙 a).hom :=
-- begin
--   simp only [category.assoc],
--   congr' 2,
--   coherence
-- end

-- meta def to_free₁ (q : parse texpr) : tactic unit :=
-- do
--   f ← tactic.i_to_expr q,
--   f' ← tactic.bicategory.free₁ f,
--   tactic.exact f'

-- meta def to_free₂ : tactic unit :=
-- do
--   η ← get_goal,
--   η' ← tactic.bicategory.free₂ η,
--   tactic.exact η'

-- end interactive

-- end tactic

-- namespace category_theory
-- universes w v u
-- variables {B : Type u} [bicategory.{w v} B]
-- variables {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
-- open_locale bicategory

-- namespace free_bicategory

-- @[simp]
-- lemma lift_id_of_eq_self (f : a ⟶ b) :
--   (lift (prefunctor.id B)).map (of.map f) = f :=
-- rfl

-- class coherence_eq (f g : a ⟶ b) :=
-- (out : of.map f ⟶ of.map g)

-- def coherence_eq_to_hom (f g : a ⟶ b) [coherence_eq f g] : f ⟶ g :=
-- eq_to_hom (lift_id_of_eq_self f).symm ≫
--   (lift (prefunctor.id B)).map₂ coherence_eq.out ≫ eq_to_hom (lift_id_of_eq_self g)

-- end free_bicategory

-- end category_theory
