import combinatorics.hales_jewett
import data.fintype.sort
import combinatorics.pigeonhole

open option function combinatorics

instance with_top.fintype {α} [fintype α] : fintype (with_top α) := option.fintype

def with_top.map {α β} [partial_order α] [partial_order β] (f : α →ₘ β) :
  with_top α →ₘ with_top β :=
{ to_fun := option.map f,
  monotone' := begin
    intros i j ij, cases i,
    { cases top_le_iff.mp ij, exact le_refl _, },
    cases j, { exact order_top.le_top _, },
    simp only [option.map_some', with_top.some_le_some],
    exact f.mono (with_top.some_le_some.mp ij),
  end }

def option.disjoint {α β} (a : option α) (b : option β) : Prop := a = none ∨ b = none

lemma option.disjoint.orelse_comm {α} {a b : option α} (h : a.disjoint b) :
  (a <|> b) = (b <|> a) :=
by rcases h with rfl | rfl; simp only [orelse_none, none_orelse]

lemma option.mem_orelse {α} {a b : option α} {x : α} (h : x ∈ (a <|> b)) : x ∈ a ∨ x ∈ b :=
begin
  cases a, { right, simpa only [mem_def, none_orelse] using h }, { left, simpa only using h}
end

def order_iso_of_card_eq {α β} [fintype α] [fintype β] [linear_order α] [linear_order β]
  (h : fintype.card α = fintype.card β) : α ≃o β :=
(mono_equiv_of_fin α rfl).symm.trans $ (fin.cast h).trans $ mono_equiv_of_fin β rfl

section bla

variables (R : Type) [monoid_with_zero R]

@[ext] structure P :=
(set : set R)
(finite : set.finite)
(zero_mem : (0 : R) ∈ set)
(one_mem : (1 : R) ∈ set)

instance : preorder (P R) := preorder.lift P.set

instance : monoid (P R) :=
{ mul := λ p q,
  { set := set.image2 (*) p.set q.set,
    finite := set.finite.image2 _ p.finite q.finite,
    zero_mem := ⟨0, 0, p.zero_mem, q.zero_mem, mul_zero 0⟩,
    one_mem := ⟨1, 1, p.one_mem, q.one_mem, mul_one 1⟩ },
  mul_assoc := λ p q r, P.ext _ _
    (by { dsimp only, rw [set.image2_image2_left, set.image2_image2_right], simp_rw mul_assoc }),
  one :=
    { set := {0, 1},
      finite := set.finite.insert _ (set.finite_singleton _),
      zero_mem := set.mem_insert 0 {1},
      one_mem := set.mem_insert_of_mem 0 rfl },
  one_mul := λ p, begin ext, split,
    { rintro ⟨_, _, rfl | rfl | _, hp, rfl⟩,
      { rw zero_mul, apply p.zero_mem }, { erw one_mul, exact hp } },
    { intro hp, exact ⟨_, _, P.one_mem _, hp, one_mul _⟩, }
  end,
  mul_one := λ p, begin ext, split,
    { rintro ⟨_, _, hp, rfl | rfl | _, rfl⟩,
      { rw mul_zero, apply p.zero_mem }, { erw mul_one, exact hp } },
    { intro hp, exact ⟨_, _, hp, P.one_mem _, mul_one _⟩, }
  end }

variables {R} (m n k : Type) [linear_order m] [linear_order n] [linear_order k] (p q r : P R)

structure inc : Type :=
(emb : m →ₘ n)
(mat : n → option (R × m))
(coeffs : P R)
(mat_emb : ∀ i, mat (emb i) = some (1, i))
(le_emb : ∀ {j} (x ∈ mat j), j ≤ emb (prod.snd x))
(mat_mem : ∀ j (x ∈ mat j), (prod.fst x) ∈ coeffs.set)
(mul_coeffs_le : p * coeffs ≤ q)

@[ext] structure vec : Type :=
(to_fun : m → R)
(mem : ∀ i, to_fun i ∈ p.set)

variable {m}

@[ext] structure row (i : m) extends vec m p :=
(eq_one : to_fun i = 1)
(le_of_ne_zero : ∀ {j}, to_fun j ≠ 0 → j ≤ i)

variables {m n k p q r}

def inc.map_vec (f : inc m n p q) (v : vec m p) : vec n q :=
{ to_fun := λ j, (f.mat j).elim 0 (λ x, v.to_fun x.snd * x.fst),
  mem :=
    begin
      intro j,
      set o := f.mat j with ho, clear_value o, cases o with x,
      { exact q.zero_mem },
      { apply f.mul_coeffs_le, refine set.mem_image2_of_mem (v.mem _) (f.mat_mem j _ _),
        rw ←ho, exact rfl }
    end }

def inc.map_row {i : m} (f : inc m n p q) (v : row p i) : row q (f.emb i) :=
{ le_of_ne_zero :=
  begin
    intros j ne,
    simp_rw [inc.map_vec] at ne,
    set o := f.mat j with ho, clear_value o, cases o with x,
    { exfalso, exact ne rfl },
    { refine le_trans (f.le_emb _ _) (f.emb.monotone $ v.le_of_ne_zero $ left_ne_zero_of_mul ne),
      rw ←ho, exact rfl, }
  end,
  eq_one := by simp_rw [inc.map_vec, f.mat_emb i, option.elim, v.eq_one, one_mul],
  ..f.map_vec v.to_vec }

def inc.comp (g : inc n k q r) (f : inc m n p q) : inc m k p r :=
{ emb := g.emb.comp f.emb,
  mat := λ c, g.mat c >>= λ y, (f.mat y.snd).map $ λ x, (x.fst * y.fst, x.snd),
  coeffs := f.coeffs * g.coeffs,
  mat_emb := λ i, by simp only [inc.mat_emb, mul_one, some_bind, map_some', preorder_hom.comp_coe],
  le_emb := λ j x h, begin
      simp only [mem_def, bind_eq_some, map_eq_some'] at h,
      obtain ⟨y, hy, x, hx, rfl⟩ := h,
      convert le_trans (g.le_emb y hy) (g.emb.monotone $ f.le_emb x hx),
    end,
  mat_mem := λ j x h, begin
      simp only [mem_def, bind_eq_some, map_eq_some'] at h,
      obtain ⟨y, hy, x, hx, rfl⟩ := h,
      exact set.mem_image2_of_mem (f.mat_mem y.snd _ hx) (g.mat_mem j _ hy),
    end,
  mul_coeffs_le := begin
      rintros _ ⟨x, _, hx, ⟨y, z, hy, hz, rfl⟩, rfl⟩,
      rw ←mul_assoc, exact g.mul_coeffs_le (set.mem_image2_of_mem
        (f.mul_coeffs_le $ set.mem_image2_of_mem hx hy) hz),
    end }

lemma inc.comp_map (f : inc m n p q) (g : inc n k q r) (v : vec m p) :
  (g.comp f).map_vec v = g.map_vec (f.map_vec v) :=
begin
  ext j,
  simp only [inc.map_vec, inc.comp],
  set o := g.mat j, clear_value o, cases o with x,
  { refl },
  simp only [option.elim, some_bind],
  set o := f.mat x.snd, clear_value o, cases o with y,
  { simp only [map_none', option.elim, zero_mul], },
  { simp only [option.elim, map_some', mul_assoc], }
end

variables (m p) (κ : Type)

def coloring : Type := ∀ i : m, row p i → κ

variables {m p κ} (co : coloring n q κ)

def coloring.restrict (f : inc m n p q) : coloring m p κ :=
λ i v, co _ (f.map_row v)

def coloring.mono_row (k : κ) (i : n) : Prop := ∀ v, co i v = k
def coloring.mono (k : κ) : Prop := ∀ i, co.mono_row k i

lemma coloring.restrict_mono_row {k : κ} {i : m} {f : inc m n p q}
  (h : co.mono_row k (f.emb i)) : (co.restrict f).mono_row k i := λ v, h _

def inc_of_le (h : p ≤ q) : inc m m p q :=
{ emb := preorder_hom.id,
  mat := λ i, some (1, i),
  coeffs := 1,
  mat_emb := λ _, rfl,
  le_emb := λ j x hx, by { rw [mem_def, (some_injective _).eq_iff] at hx, rw ←hx, refl, },
  mat_mem := λ j x hx, by { rw [mem_def, (some_injective _).eq_iff] at hx, rw ←hx, apply P.one_mem },
  mul_coeffs_le := by { rw mul_one, exact h } }

def inc.extend (f : inc m n p q) (v : n → option R) (mem : ∀ j (x ∈ v j), x ∈ f.coeffs.set)
  (h : ∀ j, (v j).disjoint (f.mat j)) : inc (with_top m) (with_top n) p q :=
{ emb := with_top.map f.emb,
  mat := λ o, option.elim o (some (1, ⊤)) $
    λ j, (v j).map (λ r, (r, ⊤)) <|> (f.mat j).map (λ p, (p.fst, some p.snd)),
  coeffs := f.coeffs,
  mat_emb := begin
      intro o, cases o with i, { refl },
      simp only [with_top.map, option.elim, map_some', preorder_hom.coe_fun_mk],
      cases h (f.emb i) with h1 h2,
      { simp only [h1, none_orelse, map_none', f.mat_emb, map_some'] },
      { exfalso, rw f.mat_emb at h2, cases h2 }
    end,
  le_emb := begin
      rintros j ⟨r, i⟩ h, cases i, { exact order_top.le_top _ },
      cases j, { cases h },
      cases option.mem_orelse h with h1 h1,
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨_, _, ⟨⟩⟩ },
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨⟨_, k⟩, ha, hb⟩,
        apply with_top.coe_le_coe.mpr, cases hb, exact f.le_emb _ ha },
    end,
  mat_mem := begin
      intros j x h,
      cases j, { simp only [mem_def, option.elim] at h, rw ←h, apply P.one_mem, },
      cases option.mem_orelse h with h1 h1,
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨a, av, ha⟩, rw ←ha, exact mem _ _ av },
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨a, af, ha⟩, rw ←ha,
        exact f.mat_mem _ _ af }
    end,
  mul_coeffs_le := f.mul_coeffs_le }

end bla

section ugh

parameters {R m n : Type} [monoid_with_zero R] [linear_order m] [linear_order n] [fintype n]
  [fintype m]
  {p : P R} (f : n → option m) (h : ∀ i, ∃ j, f j = some i)
include h

def m' : Type := m

def g (i : m') : n :=
finset.max' (finset.univ.filter $ λ j, f j = some i)
((h i).imp $ λ j hj, finset.mem_filter.mpr ⟨finset.mem_univ _, hj⟩)

lemma fg_eq_some (i : m') : f (g i) = some i :=
begin
  have : g i ∈ finset.univ.filter (λ j, f j = some i) := finset.max'_mem _ _,
  simpa only [true_and, finset.mem_univ, finset.mem_filter] using this,
end

lemma inj : injective g := λ i j ij, some_injective _ (by rw [←fg_eq_some, ←fg_eq_some, ij])


instance : fintype m' := show fintype m, from infer_instance
instance : linear_order m' := linear_order.lift g inj

def g_mono : m' →ₘ n := { to_fun := g, monotone' := λ i j, id }
def mm' : m ≃o m' := order_iso_of_card_eq rfl

def inc_of_this : inc m n p p :=
{ emb := g_mono.comp (order_embedding.to_preorder_hom mm'.to_rel_embedding),
  mat := λ j, (f j).elim none $ λ i : m', some (1, mm'.symm i),
  coeffs := 1,
  mat_emb := λ i, by simp only [g_mono, order_embedding.to_preorder_hom_coe,
    rel_iso.to_rel_embedding_eq_coe, rel_iso.coe_coe_fn, preorder_hom.coe_fun_mk,
    preorder_hom.comp_coe, fg_eq_some (mm' i), option.elim, order_iso.symm_apply_apply],
  le_emb := λ j x hx, finset.le_max' _ _ begin
      simp only [order_embedding.to_preorder_hom_coe, true_and, rel_iso.to_rel_embedding_eq_coe,
        rel_iso.coe_coe_fn, finset.mem_univ, finset.mem_filter],
      set o := f j, clear_value o, cases o, { cases hx },
      { simp only [mem_def, option.elim] at hx, simp only [←hx, mm'.apply_symm_apply], }
    end,
  mat_mem := begin
    intros, set o := f j, clear_value o, cases o, { cases H },
    { simp only [mem_def, option.elim] at H, cases H, apply P.one_mem, }
  end,
  mul_coeffs_le := by { rw mul_one, exact le_refl _, } }

end ugh

variables {R : Type} [monoid_with_zero R] (α β γ : Type) (p q : P R) (κ ι : Type)
  [linear_order α] [fintype α]
  [linear_order β] [fintype β]
  [linear_order γ] [fintype γ]
  [linear_order ι] [fintype ι]

def large_enough : Prop := ∀ co : coloring β q κ, ∃ (f : inc α β p q) (k : α → κ), ∀ i,
  (co.restrict f).mono_row (k i) i

lemma claim (h1 : large_enough α β p q κ) (h2 : extended_HJ_works q.set κ ι β) :
  large_enough (with_top α) (with_top ι) p (q * p) κ :=
begin
  intro co,
end
