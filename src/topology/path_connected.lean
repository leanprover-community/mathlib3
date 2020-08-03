import topology.instances.real

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `joined (x y : X)` means there is a continuous `γ : I → X`, such that `γ 0 = x` and `γ 1 = y`.
* `path_component (x : X)` is the set of points joined to `x`.
* `path_connected_space X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : set X`.

* `joined_in F (x y : X)` means there is a continuous `γ : I → X` with values in `F`,
  such that `γ 0 = x` and `γ 1 = y`.
* `path_component_in F (x : X)` is the set of points joined to `x` in `F`.
* `is_path_connected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `loc_path_connected_space X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `joined` and `joined_in F` are transitive relations.

One can link the absolute and relative version in two direction, using `(univ : set X)` or the
subtype `↥F`.

* `path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X)`
* `is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space ↥F`

For locally path connected spaces, we have
* `path_connected_space_iff_connected_space : path_connected_space X ↔ connected_space X`
* `is_connected_iff_is_path_connected (U_op : is_open U) : is_path_connected  U ↔ is_connected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `I_extend` that will extend any continuous map `γ : I → X` into a continuous map
`I_extend γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `joined.extend` that turns `h : joined x y` into a continuous map
`h.extend : ℝ → X` whose restriction to `I` joins `x` and `y`.

Similarly, one can turn `h : joined_in F x y` into a continuous map
`h.extend : ℝ → X`, and `h.map : I → F` taking values in the subtype `F`,
and also `h.extend_map : ℝ → F`.

-/

noncomputable theory
open_locale classical topological_space filter
open filter set

variables {X : Type*} [topological_space X] {x y z : X} {ι : Type*}

local notation `I` := Icc (0 : ℝ) 1

lemma Icc_zero_one_symm {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

instance I_has_zero : has_zero I := ⟨⟨0, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_I_zero : ((0 : I) : ℝ) = 0 := rfl

instance I_has_one : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_I_one : ((1 : I) : ℝ) = 1 := rfl

/-- Unit interval central symmetry. -/
def I_symm : I → I := λ t, ⟨1 - t.val, Icc_zero_one_symm.mp t.property⟩

local notation `σ` := I_symm

@[simp] lemma I_symm_zero : σ 0 = 1 :=
subtype.ext $ by simp [I_symm]

@[simp] lemma I_symm_one : σ 1 = 0 :=
subtype.ext $ by simp [I_symm]

@[continuity]
lemma continuous_I_symm : continuous σ :=
by continuity!

/-- Projection of `ℝ` onto its unit interval. -/
def proj_I : ℝ → I :=
λ t, if h : t ≤ 0 then ⟨0, left_mem_Icc.mpr zero_le_one⟩ else
     if h' : t ≤ 1 then ⟨t, ⟨le_of_lt $ not_le.mp h, h'⟩⟩ else ⟨1, right_mem_Icc.mpr zero_le_one⟩

lemma proj_I_I {t : ℝ} (h : t ∈ I) : proj_I t = ⟨t, h⟩ :=
begin
  unfold proj_I,
  rw mem_Icc at h,
  split_ifs,
  { simp [show t = 0, by linarith] },
  { refl },
  { exfalso, linarith }
end

lemma range_proj_I : range proj_I = univ :=
begin
  rw eq_univ_iff_forall,
  rintro ⟨t, t_in⟩,
  use [t, proj_I_I t_in],
end

lemma continuous_proj_I : continuous proj_I :=
begin
  refine continuous_induced_rng' (coe : I → ℝ) rfl _,
  have : continuous (λ t : ℝ, if t ≤ 0 then 0 else if t ≤ 1 then t else 1),
  { refine continuous_if _ continuous_const (continuous_if _ continuous_id continuous_const) ;
    simp [Iic_def, zero_le_one] },
  convert this,
  ext,
  dsimp [proj_I],
  split_ifs ; refl
end

variables {β : Type*}

/-- Extension of a function defined on the unit interval to `ℝ`, by precomposing with
the projection. -/
def I_extend {β : Type*} (f : I → β) : ℝ → β :=
f ∘ proj_I

@[continuity]
lemma continuous.I_extend {f : I → X} (hf : continuous f) : continuous (I_extend f) :=
hf.comp continuous_proj_I

lemma I_extend_extends (f : I → β) {t : ℝ} (ht : t ∈ I) : I_extend f t = f ⟨t, ht⟩ :=
by simp [I_extend, proj_I_I, ht]

@[simp] lemma I_extend_zero (f : I → β) : I_extend f 0 = f 0 :=
I_extend_extends _ _

@[simp] lemma I_extend_one (f : I → β) : I_extend f 1 = f 1 :=
I_extend_extends _ _

@[simp] lemma I_extend_range (f : I → β) : range (I_extend f) = range f :=
begin
  rw [I_extend, range_comp],
  convert image_univ,
  exact range_proj_I
end

instance : connected_space I := subtype.connected_space ⟨⟨0, by split ; norm_num⟩, is_preconnected_Icc⟩

/-- The relation "being joined by a path". This is an equivalence relation. -/
def joined (x y : X) : Prop := ∃ γ : I → X, continuous γ ∧ γ 0 = x ∧ γ 1 = y

lemma joined.refl (x : X) : joined x x :=
⟨λ t, x, by continuity, rfl, rfl⟩

lemma joined.symm {x y : X} : joined x y → joined y x
| ⟨γ, γ_cont, γ_src, γ_tgt⟩ := ⟨γ ∘ σ, by continuity, by simpa using γ_tgt, by simpa using γ_src⟩

/-- Continuous map from `ℝ` to `X` when `x` and `y` are joined. -/
def joined.extend {x y : X} (h : joined x y) : ℝ → X := I_extend (classical.some h)

lemma joined.continuous_extend {x y : X} (h : joined x y) : continuous h.extend :=
(classical.some_spec h).1.I_extend

lemma joined.extend_zero {x y : X} (h : joined x y) : h.extend 0 = x :=
by simp [joined.extend, (classical.some_spec h).2.1]

lemma joined.extend_one {x y : X} (h : joined x y) : h.extend 1 = y :=
by simp [joined.extend, (classical.some_spec h).2.2]

local attribute [simp] Iic_def

lemma joined.trans {x y z : X} (hxy : joined x y) (hyz : joined y z) :
  joined x z :=
begin
  rcases hxy with ⟨f, f_cont, f_src, f_tgt⟩,
  rcases hyz with ⟨g, g_cont, g_src, g_tgt⟩,
  refine ⟨(λ t : ℝ, if t ≤ 1/2 then I_extend f (2*t) else I_extend g (2*t-1)) ∘ coe, _, _, _⟩,
  { apply (continuous_if _ _ _).comp continuous_subtype_coe,
    { norm_num,
      rw [f_tgt, g_src] },
    { exact f_cont.I_extend.comp (continuous_const.mul continuous_id') },
    { exact g_cont.I_extend.comp ((continuous_const.mul continuous_id').sub continuous_const) }},
  { simp [zero_le_one, I_extend_zero, f_src] },
  { norm_num,
    simp [I_extend_one, g_tgt] },
end

variables (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def path_setoid : setoid X :=
{ r := joined,
  iseqv := mk_equivalence  _ joined.refl (λ x y, joined.symm) (λ x y z, joined.trans) }

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def zeroth_homotopy := quotient (path_setoid X)

instance : inhabited (zeroth_homotopy ℝ) := ⟨@quotient.mk ℝ (path_setoid ℝ) 0⟩

variables {X}

/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def joined_in (F : set X) (x y : X) : Prop :=
∃ γ : I → X, continuous γ ∧ (∀ t, γ t ∈ F) ∧ γ 0 = x ∧ γ 1 = y

variables {F : set X}

lemma joined_in.mem (h : joined_in F x y) : x ∈ F ∧ y ∈ F :=
begin
  rcases h with ⟨γ, γ_cont, γ_in, γ_src, γ_tgt⟩,
  split ; [rw ← γ_src, rw ← γ_tgt] ; apply γ_in ; norm_num
end

lemma joined_in.mem_left (h : joined_in F x y) : x ∈ F :=
h.mem.1

lemma joined_in.mem_right (h : joined_in F x y) : y ∈ F :=
h.mem.2

/-- Continuous map from `ℝ` to `X` when `x` and `y` are joined in `F`. -/
def joined_in.extend (h : joined_in F x y) : ℝ → X := I_extend (classical.some h)

lemma joined_in.continuous_extend (h : joined_in F x y) : continuous h.extend :=
(classical.some_spec h).1.I_extend

lemma joined_in.extend_zero (h : joined_in F x y) : h.extend 0 = x :=
by rw [joined_in.extend, I_extend_zero, (classical.some_spec h).2.2.1]

lemma joined_in.extend_one (h : joined_in F x y) : h.extend 1 = y :=
by rw [joined_in.extend, I_extend_one, (classical.some_spec h).2.2.2]

/-- Continuous map from `I` to `F` when `x` and `y` are joined in `F`. -/
def joined_in.map (h : joined_in F x y) : I → F :=
λ t, ⟨classical.some h t, (classical.some_spec h).2.1 t⟩

lemma joined_in.continuous_map (h : joined_in F x y) : continuous h.map :=
continuous_subtype_mk _ (classical.some_spec h).1

lemma joined_in.map_zero (h : joined_in F x y) : h.map 0 = ⟨x, h.mem.1⟩:=
subtype.ext (classical.some_spec h).2.2.1

lemma joined_in.map_one (h : joined_in F x y) : h.map 1 = ⟨y, h.mem.2⟩:=
subtype.ext (classical.some_spec h).2.2.2

/-- Continuous map from `ℝ` to `F` when `x` and `y` are joined in `F`. -/
def joined_in.extend_map (h : joined_in F x y) : ℝ → F :=
I_extend h.map

lemma joined_in.extend_map_continuous (h : joined_in F x y) : continuous h.extend_map :=
h.continuous_map.I_extend

lemma joined_in.extend_map_zero (h : joined_in F x y) : h.extend_map 0 = ⟨x, h.mem.1⟩ :=
by rw [joined_in.extend_map, I_extend_zero, h.map_zero]

lemma joined_in.extend_map_one (h : joined_in F x y) : h.extend_map 1 = ⟨y, h.mem.2⟩ :=
by rw [joined_in.extend_map, I_extend_one, h.map_one]

lemma joined_in.joined : joined_in F x y → joined x y
| ⟨γ, γ_cont, γ_in, γ_src, γ_tgt⟩ := ⟨γ, γ_cont, γ_src, γ_tgt⟩

lemma joined_in_iff_joined (hx : x ∈ F) (hy : y ∈ F) :
  joined_in F x y ↔ joined (⟨x, hx⟩ : F) (⟨y, hy⟩ : F) :=
⟨λ h,⟨h.map, h.continuous_map, h.map_zero, h.map_one⟩,
 λ ⟨γ, γ_cont, γ_src, γ_tgt⟩,
   ⟨coe ∘ γ, continuous_subtype_coe.comp γ_cont, by simp, by simp [γ_src], by simp [γ_tgt]⟩⟩

@[simp] lemma joined_in_univ : joined_in univ x y ↔ joined x y :=
by simp [joined_in, joined]

lemma joined_in.mono {U V : set X} (h : joined_in U x y) (hUV : U ⊆ V) : joined_in V x y :=
let ⟨f, f_cont, f_in, f_src, f_tgt⟩ := h in ⟨f, f_cont, λ t, hUV (f_in t), f_src, f_tgt⟩

lemma joined_in.refl (h : x ∈ F) : joined_in F x x :=
⟨λ t, x, continuous_const, λ t, h, rfl, rfl⟩

lemma joined_in.symm (h : joined_in F x y) : joined_in F y x :=
begin
  cases h.mem with hx hy,
  simp [joined_in_iff_joined, *] at *,
  exact h.symm
end

lemma joined_in.trans (hxy : joined_in F x y) (hyz : joined_in F y z) : joined_in F x z :=
begin
  cases hxy.mem with hx hy,
  cases hyz.mem with hx hy,
  simp [joined_in_iff_joined, *] at *,
  exact hxy.trans hyz
end

/-- The path component of `x` is the set of points that can be joined to `x`. -/
def path_component (x : X) := {y | joined x y}

@[simp] lemma mem_path_component_self (x : X) : x ∈ path_component x :=
joined.refl x

@[simp] lemma path_component.nonempty (x : X) : (path_component x).nonempty :=
⟨x, mem_path_component_self x⟩

lemma mem_path_component_of_mem (h : x ∈ path_component y) : y ∈ path_component x :=
joined.symm h

lemma path_component_symm : x ∈ path_component y ↔ y ∈ path_component x :=
⟨λ h, mem_path_component_of_mem h, λ h, mem_path_component_of_mem h⟩

lemma path_component_congr (h : x ∈ path_component y) : path_component x = path_component y:=
begin
  ext z,
  split,
  { intro h',
    rw path_component_symm,
    exact (h.trans h').symm },
  { intro h',
    rw path_component_symm at h' ⊢,
    exact h'.trans h },
end

lemma path_component_subset_component (x : X) : path_component x ⊆ connected_component x :=
λ y ⟨f, f_cont, f_src, f_tgt⟩, subset_connected_component (is_connected_range f_cont).2 ⟨0, f_src⟩ ⟨1, f_tgt⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def path_component_in (x : X) (F : set X) := {y | joined_in F x y}

@[simp] lemma path_component_in_univ (x : X) : path_component_in x univ = path_component x :=
by simp [path_component_in, path_component, joined_in, joined]

lemma joined.mem_path_component (hyz : joined y z) (hxy : y ∈ path_component x) : z ∈ path_component x :=
hxy.trans hyz

/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def is_path_connected (F : set X) : Prop := ∃ x ∈ F, ∀ {y}, y ∈ F → joined_in F x y

lemma is_path_connected_iff_eq : is_path_connected F ↔  ∃ x ∈ F, path_component_in x F = F :=
begin
  split ; rintros ⟨x, x_in, h⟩ ; use [x, x_in],
  { ext y,
    exact ⟨λ hy, hy.mem.2, h⟩ },
  { intros y y_in,
    rwa ← h at y_in },
end

lemma is_path_connected.joined_in (h : is_path_connected F) : ∀ x y ∈ F, joined_in F x y :=
λ x y x_in y_in, let ⟨b, b_in, hb⟩ := h in (hb x_in).symm.trans (hb y_in)

lemma is_path_connected_iff : is_path_connected F ↔ F.nonempty ∧ ∀ x y ∈ F, joined_in F x y :=
⟨λ h, ⟨let ⟨b, b_in, hb⟩ := h in ⟨b, b_in⟩, h.joined_in⟩,
 λ ⟨⟨b, b_in⟩, h⟩, ⟨b, b_in, λ x x_in, h b x b_in x_in⟩⟩

lemma is_path_connected.image {Y : Type*} [topological_space Y] (hF : is_path_connected F)
  {f : X → Y} (hf : continuous f) : is_path_connected (f '' F) :=
begin
  rcases hF with ⟨x, x_in, hx⟩,
  use [f x, mem_image_of_mem f x_in],
  rintros _ ⟨y, y_in, rfl⟩,
  rcases hx y_in with ⟨γ, γ_cont, γ_in, rfl, rfl⟩,
  use [f ∘ γ, hf.comp γ_cont, λ t, ⟨γ t, γ_in t, rfl⟩, rfl, rfl]
end

lemma is_path_connected.mem_path_component (h : is_path_connected F) (x_in : x ∈ F) (y_in : y ∈ F) :
  y ∈ path_component x :=
(h.joined_in x y x_in y_in).joined

lemma  is_path_connected.subset_path_component (h : is_path_connected F) (x_in : x ∈ F) :
  F ⊆ path_component x :=
λ y y_in, h.mem_path_component x_in y_in

lemma is_path_connected.union {U V : set X} (hU : is_path_connected U) (hV : is_path_connected V)
  (hUV : (U ∩ V).nonempty) : is_path_connected (U ∪ V) :=
begin
  rcases hUV with ⟨x, xU, xV⟩,
  use [x, or.inl xU],
  rintros y (yU | yV),
  { exact (hU.joined_in x y xU yU).mono (subset_union_left U V) },
  { exact (hV.joined_in x y xV yV).mono (subset_union_right U V) },
end

lemma is_path_connected.preimage_coe {U W : set X} (hW : is_path_connected W) (hWU : W ⊆ U) :
  is_path_connected ((coe : U → X) ⁻¹' W) :=
begin
  rcases hW with ⟨x, x_in, hx⟩,
  use [⟨x, hWU x_in⟩, by simp [x_in]],
  rintros ⟨y, hyU⟩ hyW,
  change y ∈ W at hyW,
  rcases hx hyW with ⟨γ, γ_cont, γ_mem, rfl, rfl⟩,
  exact ⟨λ t, ⟨γ t, hWU $ γ_mem t⟩, continuous_subtype_mk _ γ_cont, γ_mem, rfl, rfl⟩,
end

/-- A topological space is path-connected if it is non-empy and every two points can be
joined by a continuous path. -/
class path_connected_space (X : Type*) [topological_space X] : Prop :=
(nonempty : nonempty X)
(joined : ∀ x y : X, joined x y)

attribute [instance, priority 50] path_connected_space.nonempty

lemma path_connected_space_iff_zeroth_homotopy :
  path_connected_space X ↔ nonempty (zeroth_homotopy X) ∧ subsingleton (zeroth_homotopy X) :=
begin
  letI := path_setoid X,
  split,
  { introI h,
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨_⟩⟩,
    rintros ⟨x⟩ ⟨y⟩,
    exact quotient.sound (path_connected_space.joined x y) },
  { unfold zeroth_homotopy,
    rintros ⟨h, h'⟩,
    resetI,
    exact ⟨(nonempty_quotient_iff _).mp h, λ x y, quotient.exact $ subsingleton.elim ⟦x⟧ ⟦y⟧⟩ },
end

namespace path_connected_space
variables [path_connected_space X]

/-- Use path-connectedness to build a path between two points. -/
def path (x y : X) : I → X :=
classical.some (joined x y)

lemma continuous_path (x y : X) : continuous (path x y) :=
(classical.some_spec (joined x y)).1

lemma path_zero (x y : X) : path x y 0 = x :=
(classical.some_spec (joined x y)).2.1

lemma path_one (x y : X) : path x y 1 = y :=
(classical.some_spec (joined x y)).2.2

end path_connected_space

lemma is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space F :=
begin
  rw is_path_connected_iff,
  split,
  { rintro ⟨⟨x, x_in⟩, h⟩,
    refine ⟨⟨⟨x, x_in⟩⟩, _⟩,
    rintros ⟨y, y_in⟩ ⟨z, z_in⟩,
    have H := h y z y_in z_in,
    rwa joined_in_iff_joined y_in z_in at H },
  { rintros ⟨⟨x, x_in⟩, H⟩,
    refine ⟨⟨x, x_in⟩, λ y z y_in z_in, _⟩,
    rcases H ⟨y, y_in⟩ ⟨z, z_in⟩ with ⟨f, f_cont, f_src, f_tgt⟩,
    use [coe ∘ f, by continuity!],
    simp [*] }
end

lemma path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X) :=
begin
  split,
  { introI h,
    inhabit X,
    refine ⟨default X, mem_univ _, _⟩,
    simpa [joined_in] using  path_connected_space.joined (default X) },
  { intro h,
    have h' := h.joined_in,
    cases h with x h,
    exact ⟨⟨x⟩, by simpa using h'⟩ },
end

lemma path_connected_space_iff_eq : path_connected_space X ↔ ∃ x : X, path_component x = univ :=
by simp [path_connected_space_iff_univ, is_path_connected_iff_eq]

@[priority 100] -- see Note [lower instance priority]
instance path_connected_space.connected_space [path_connected_space X] : connected_space X :=
begin
  rw connected_space_iff_connected_component,
  rcases is_path_connected_iff_eq.mp (path_connected_space_iff_univ.mp ‹_›) with ⟨x, x_in, hx⟩,
  use x,
  rw ← univ_subset_iff,
  exact (by simpa using hx : path_component x = univ) ▸ path_component_subset_component x
end

/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class loc_path_connected_space (X : Type*) [topological_space X] : Prop :=
(path_connected_basis : ∀ x : X, (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s) id)

export loc_path_connected_space (path_connected_basis)

lemma loc_path_connected_of_bases {p : ι → Prop} {s : X → ι → set X}
  (h : ∀ x, (𝓝 x).has_basis p (s x)) (h' : ∀ x i, p i → is_path_connected (s x i)) :
  loc_path_connected_space X :=
begin
  constructor,
  intro x,
  apply (h x).to_has_basis,
  { intros  i pi,
    exact ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩, by refl⟩ },
  { rintros U ⟨U_in, hU⟩,
    rcases (h x).mem_iff.mp U_in with ⟨i, pi, hi⟩,
    tauto }
end

lemma path_connected_space_iff_connected_space [loc_path_connected_space X] :
  path_connected_space X ↔ connected_space X :=
begin
  split,
  { introI h,
    apply_instance },
  { introI hX,
    inhabit X,
    let x₀ := default X,
    rw path_connected_space_iff_eq,
    use x₀,
    refine eq_univ_of_nonempty_clopen (by simp) ⟨_, _⟩,
    { rw is_open_iff_mem_nhds,
      intros y y_in,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      apply mem_sets_of_superset U_in,
      rw ← path_component_congr y_in,
      exact hU.subset_path_component (mem_of_nhds U_in) },
    { rw is_closed_iff_nhds,
      intros y H,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      rcases H U U_in with ⟨z, hz, hz'⟩,
      exact ((hU.joined_in z y hz $ mem_of_nhds U_in).joined.mem_path_component hz') } },
end

lemma path_connected_subset_basis [loc_path_connected_space X] {U : set X} (h : is_open U)
  (hx : x ∈ U) : (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s ∧ s ⊆ U) id :=
(path_connected_basis x).has_basis_self_subset (mem_nhds_sets h hx)

lemma loc_path_connected_of_is_open [loc_path_connected_space X] {U : set X} (h : is_open U) :
  loc_path_connected_space U :=
⟨begin
  rintros ⟨x, x_in⟩,
  rw nhds_subtype_eq_comap,
  constructor,
  intros V,
  rw (has_basis.comap (coe : U → X) (path_connected_subset_basis h x_in)).mem_iff,
  split,
  { rintros ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩,
    exact ⟨coe ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩ },
  { rintros ⟨W, ⟨W_in, hW⟩, hWV⟩,
    refine ⟨coe '' W, ⟨filter.image_coe_mem_sets (mem_nhds_sets h x_in) W_in,
                       hW.image continuous_subtype_coe, subtype.coe_image_subset U W⟩, _⟩,
    rintros x ⟨y, ⟨y_in, hy⟩⟩,
    rw ← subtype.coe_injective hy,
    tauto },
end⟩

lemma is_open.is_connected_iff_is_path_connected [loc_path_connected_space X] {U : set X} (U_op : is_open U) :
 is_path_connected  U ↔ is_connected U :=
begin
  rw [is_connected_iff_connected_space, is_path_connected_iff_path_connected_space],
  haveI := loc_path_connected_of_is_open U_op,
  exact path_connected_space_iff_connected_space
end
