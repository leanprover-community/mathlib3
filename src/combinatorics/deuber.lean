import combinatorics.hales_jewett
import group_theory.submonoid
import combinatorics.pigeonhole
import data.fintype.sort
import data.finsupp
import data.matrix.basic

open_locale big_operators classical matrix
noncomputable theory

instance with_top.fintype {α} [fintype α] : fintype (with_top α) := option.fintype

def with_top.order_embedding {α : Type} [linear_order α] : α ↪o with_top α :=
order_embedding.of_map_le_iff coe (λ _ _, with_top.coe_le_coe)

def some_linear_order {α} [fintype α] : linear_order α :=
linear_order.lift (fintype.equiv_fin α) (equiv.injective _)

def order_iso_of_card_eq {α β} [fintype α] [fintype β] [linear_order α] [linear_order β]
  (h : fintype.card α = fintype.card β) : α ≃o β :=
(mono_equiv_of_fin α rfl).symm.trans $ (fin.cast h).trans $ mono_equiv_of_fin β rfl

def order_emb_of_card_le {α β} [fintype α] [linear_order α] [linear_order β] {s : finset β}
  (h : fintype.card α ≤ s.card) : α ↪o β :=
(mono_equiv_of_fin α rfl).symm.to_order_embedding.trans $ (fin.cast_le h).trans $
  s.order_emb_of_fin rfl

def order_emb_mem {α β} [fintype α] [linear_order α] [linear_order β] {s : finset β}
  (h : fintype.card α ≤ s.card) (a : α) : order_emb_of_card_le h a ∈ s :=
s.order_emb_of_fin_mem _ _

def ends_at_with {α M} [has_zero M] [linear_order α] (f : α → M) (i : α) (x : M) : Prop :=
  ∀ j, i ≤ j → f j = if i = j then x else 0

lemma ends_at_with.lt {α M} [has_zero M] [linear_order α] {f : α → M} {i j : α} {x : M}
  (h : ends_at_with f i x) (ij : i < j) : f j = 0 :=
by rw [h _ (le_of_lt ij), if_neg (ne_of_lt ij)]

lemma ends_at_with.self {α M} [has_zero M] [linear_order α] {f : α → M} {i : α} {x : M}
  (h : ends_at_with f i x) : f i = x :=
by rw [h _ (le_refl i), if_pos rfl]

variables {R : Type} [semiring R] (A : submonoid R)

structure PC :=
(p : set R)
(p_finite : p.finite)
(zero_mem : (0 : R) ∈ p)
(C : A)
(C_mem : (C : R) ∈ p)

structure MPC extends PC A :=
(m : Type)
(fintype : fintype m)
(linear_order : linear_order m)

variable {A}

attribute [instance] MPC.fintype MPC.linear_order

instance : inhabited (PC A) :=
⟨⟨{0, 1}, set.finite.insert 0 (set.finite_pure 1), set.mem_insert 0 {1}, 1,
  set.mem_insert_of_mem 0 rfl⟩⟩

def mk_MPC (S : PC A) (m : Type) [fintype m] [linear_order m] : MPC A :=
{ m := m, fintype := infer_instance, linear_order := infer_instance, ..S }

instance : inhabited (MPC A) := ⟨mk_MPC (default _) unit⟩

variables (S T : MPC A)

structure MPC.inclusion : Type :=
(to_fun : S.m ↪o T.m)
(mat : matrix S.m T.m R)
(scale : R)
(scale_C : (S.C : R) * scale = T.C)
(ends : ∀ i, ends_at_with (mat i) (to_fun i) scale)
(foo : T.m → option S.m)
(disj : ∀ i j, foo j ≠ some i → mat i j = 0)
(mem : ∀ i j (r ∈ S.p), r * mat i j ∈ T.p)

@[ext] structure MPC.row (i : S.m) :=
(d : S.m → R)
(d_mem : ∀ i, d i ∈ S.p)
(ends : ends_at_with d i S.C)

def MPC.trivial_inclusion {n : Type} [fintype n] [linear_order n] (f : S.m ↪o n) :
  S.inclusion (mk_MPC S.to_PC n) :=
{ to_fun := f,
  mat := λ i j, if f i = j then 1 else 0,
  scale := 1,
  scale_C := mul_one _,
  ends := λ i j ij, rfl,
  foo := function.partial_inv f,
  disj := by { intros i j ji, rw if_neg, refine mt _ ji, rintro rfl,
    rw function.partial_inv_left f.injective, },
  mem := by { intros, rw [mul_ite, mul_one, mul_zero], split_ifs, { assumption, },
    { apply PC.zero_mem, } } }

variables {S T}

lemma MPC.inclusion.sum_eq (inc : S.inclusion T) {i : S.m} {j : T.m} {x : R}
  {d : S.m → R} (ve : ends_at_with d i x) (ij : inc.to_fun i ≤ j) :
  ∑ k : S.m, d k * inc.mat k j = if inc.to_fun i = j then d i * inc.scale else 0 :=
begin
  rw [finset.sum_eq_single_of_mem i (finset.mem_univ i), inc.ends _ _ ij, mul_ite, mul_zero],
  intros k junk ki,
  cases lt_or_gt_of_ne ki,
  { rw [(inc.ends _).lt, mul_zero],
    refine lt_of_lt_of_le _ ij, rw order_embedding.lt_iff_lt, assumption, },
  { rw [ve.lt, zero_mul], assumption, },
end

def MPC.id_inc : S.inclusion S :=
{ to_fun := (order_iso.refl S.m).to_order_embedding,
  mat := 1,
  scale := 1,
  scale_C := mul_one _,
  ends := λ i j ij, rfl,
  foo := some,
  disj := λ i j ij, matrix.one_apply_ne $ ne_of_apply_ne _ ij.symm,
  mem := by { intros, rw [matrix.one_apply, mul_ite, mul_one, mul_zero], split_ifs, { assumption },
    { apply PC.zero_mem, }, } }

def MPC.inclusion.comp {U : MPC A} (f : S.inclusion T) (g : T.inclusion U) : S.inclusion U :=
{ to_fun := f.to_fun.trans g.to_fun,
  mat := f.mat ⬝ g.mat,
  scale := f.scale * g.scale,
  scale_C := by rw [←mul_assoc, f.scale_C, g.scale_C],
  ends :=
    by { intros i j ij, rw [matrix.mul_apply, g.sum_eq (f.ends _) ij, (f.ends _).self], refl },
  foo := λ x, g.foo x >>= f.foo,
  disj :=
    begin
      intros i j h,
      rw matrix.mul_apply,
      apply finset.sum_eq_zero,
      intros k junk,
      by_cases hh : g.foo j = some k,
      { rw [hh, option.some_bind] at h, rw [f.disj _ _ h, zero_mul], },
      { rw [g.disj _ _ hh, mul_zero], }
    end,
  mem :=
    begin
      intros i k r hr,
      rw matrix.mul_apply,
      set o := g.foo k with ho,
      clear_value o,
      cases o with j,
      { convert U.zero_mem, rw [finset.sum_eq_zero, mul_zero],
        intros j junk, rw [g.disj, mul_zero], rw ←ho, rintro ⟨⟩, },
      { rw [finset.sum_eq_single_of_mem j (finset.mem_univ j), ←mul_assoc],
        { apply g.mem, apply f.mem, exact hr, },
        { intros b junk bj, rw [g.disj, mul_zero],
          rw ←ho, exact (option.some_injective _).ne bj.symm, }, }
    end }

def MPC.inclusion.map_row (inc : S.inclusion T) (i : S.m) (v : S.row i) : T.row (inc.to_fun i) :=
{ d := inc.mat.vec_mul v.d,
  d_mem :=
    begin
      intro j,
      change ∑ i : S.m, v.d i * inc.mat i j ∈ _,
      set o := inc.foo j with hi,
      clear_value o,
      cases o with i,
      { convert T.zero_mem, apply finset.sum_eq_zero,
        intros i junk, rw [inc.disj, mul_zero], rw ←hi, rintro ⟨⟩, },
      { rw finset.sum_eq_single_of_mem i (finset.mem_univ i),
        { apply inc.mem, apply v.d_mem, },
        { intros i' junk ine, rw [inc.disj, mul_zero],
          rw ←hi, apply (option.some_injective _).ne, exact ine.symm, }, },
    end,
  ends := by { intros j ij, convert inc.sum_eq v.ends ij, rw [v.ends.self, inc.scale_C] } }

lemma MPC.inclusion.map_row_comp {U : MPC A} (f : S.inclusion T) (g : T.inclusion U) (i : S.m)
  (v : S.row i) : (f.comp g).map_row _ v = g.map_row _ (f.map_row _ v) :=
MPC.row.ext _ _ (matrix.vec_mul_vec_mul _ _ _).symm

variables (S T) (κ : Type)

def MPC.coloring : Type := Π i : S.m, S.row i → κ

variables {S T κ}

def MPC.coloring.restrict (co : T.coloring κ) (inc : S.inclusion T) : S.coloring κ :=
λ i v, co _ (inc.map_row _ v)

lemma MPC.coloring.restrict_comp {U : MPC A} (co : U.coloring κ) (f : S.inclusion T)
  (g : T.inclusion U) : co.restrict (f.comp g) = (co.restrict g).restrict f :=
by { funext i v, unfold MPC.coloring.restrict, congr' 1, apply f.map_row_comp, }

def MPC.coloring.row_mono (co : S.coloring κ) (i : S.m) (k : κ) : Prop := ∀ v, co i v = k
def MPC.coloring.mono (co : S.coloring κ) (k : κ) : Prop := ∀ i, co.row_mono i k

lemma MPC.coloring.restrict_mono (co : T.coloring κ) (f : S.inclusion T) (i : S.m) (k : κ)
  (h : co.row_mono (f.to_fun i) k) : (co.restrict f).row_mono i k :=
by { intro, apply h, }

def MPC.inclusion.extend {S : PC A} {m : Type} [fintype m] [linear_order m]
  (inc : (mk_MPC S m).inclusion T) (top : T.m) (lt_mtop : ∀ i, inc.to_fun i < top) :
  (mk_MPC S (with_top m)).inclusion T :=
{ to_fun := order_embedding.of_strict_mono (λ o, option.elim o top inc.to_fun)
    begin
      intros i j,
      cases i with i,
      { intro h, exfalso, refine not_lt_of_ge _ h, exact le_top, },
      cases j with j,
      { intro junk, apply lt_mtop, },
      intro h,
      simpa only [option.elim, order_embedding.lt_iff_lt] using (with_top.coe_lt_coe.mp h),
    end,
  mat := _,
  scale := _,
  scale_C := _,
  ends := _,
  foo := _,
  disj := _,
  mem := _ }

theorem deuber (κ : Type) [fintype κ] : ∃ T : MPC A, ∀ co : T.coloring κ,
  ∃ (inc : S.inclusion T) (k : κ), (co.restrict inc).mono k :=
begin
  suffices : ∀ r : ℕ, ∃ (U : Type) (ufin : fintype U) (ulin : linear_order U) (T : MPC A),
    by resetI; exact fintype.card U = r ∧ ∀ co : T.coloring κ,
      ∃ (inc : (mk_MPC S.to_PC U).inclusion T) (k : U → κ),
        ∀ i, (co.restrict inc).row_mono i (k i),
  { sorry,
    /-specialize this (fintype.card κ * fintype.card S.m + 1),
    obtain ⟨U, inst1, inst2, T, ucard, h⟩ := this,
    resetI,
    use T,
    intro co,
    specialize h co,
    obtain ⟨inc, k₀, h⟩ := h,
    obtain ⟨k, hk : fintype.card S.m < _⟩ := fintype.exists_lt_card_fiber_of_mul_lt_card k₀ _,
    swap, { rw ucard, apply lt_add_one, },
    let tinc := S.trivial_inclusion (order_emb_of_card_le (le_of_lt hk)),
    refine ⟨tinc.comp inc, k, _⟩,
    intro i,
    rw co.restrict_comp,
    apply MPC.coloring.restrict_mono,
    convert h _,
    have := order_emb_mem (le_of_lt hk) i,
    simp only [true_and, finset.mem_univ, finset.mem_filter, finset.filter_congr_decidable] at this,
    exact this.symm,-/ },
  { intro r,
    induction r with r ih,
    { refine ⟨fin 0, infer_instance, infer_instance, mk_MPC S.to_PC (fin 0), fintype.card_fin 0, _⟩,
      intro co, exact ⟨MPC.id_inc, is_empty_elim, λ (i : fin 0), is_empty_elim i⟩, },
    obtain ⟨U, inst1, inst2, T, ucard, h⟩ := ih,
    haveI : fintype T.p := T.p_finite.fintype,
    set n := T.m with hn,
    clear_value n,
    haveI : fintype n, { rw hn, apply_instance, },
    have ncard : fintype.card n = fintype.card T.m, { apply fintype.card_congr, rw hn, },
    obtain ⟨ι, inst3, hι⟩ := combinatorics.extended_HJ T.p κ n,
    resetI,
    haveI : linear_order ι := some_linear_order,
    let V : MPC A :=
    { p := set.image2 (*) T.p S.p,
      p_finite := set.finite.image2 _ T.p_finite S.p_finite,
      zero_mem := ⟨0, 0, T.zero_mem, S.zero_mem, zero_mul _⟩,
      C := T.C * S.C,
      C_mem := ⟨T.C, S.C, T.C_mem, S.C_mem, rfl⟩,
      m := with_top ι,
      linear_order := infer_instance,
      fintype := infer_instance },
    refine ⟨with_top U, infer_instance, infer_instance, V, _, _⟩,
    { erw [fintype.card_option, ucard], },
    intro co,
    specialize hι (λ v, co ⊤ ⟨λ o, option.elim o V.C (λ i, v i * S.C), _, _⟩),
    { intro o, cases o with i, { exact V.C_mem, }, { exact ⟨_, _, (v i).2, S.C_mem, rfl⟩, } },
    { intros j hj, cases top_le_iff.mp hj, rw if_pos, refl, refl, },
    obtain ⟨l, ktop, lk⟩ := hι,
    let nhead : n → ι := λ x, (finset.univ.filter $ λ y, l.idx_fun y = sum.inr x).max' _,
    swap,
    { cases l.proper x with y hy, use y, rw [finset.mem_filter], exact ⟨finset.mem_univ y, hy⟩ },
    have nhead_idx_fun : l.idx_fun ∘ nhead = sum.inr,
    { funext a, suffices : nhead a ∈ (finset.univ.filter $ λ y, l.idx_fun y = sum.inr a),
      { rw finset.mem_filter at this, exact this.2, }, apply finset.max'_mem, },
    letI : linear_order n := linear_order.lift nhead _,
    swap, { apply function.injective.of_comp, rw nhead_idx_fun, exact sum.inr_injective },
    let nhead_mono : n ↪o ι := order_embedding.of_map_le_iff nhead (λ _ _, iff.rfl),
    have mn : T.m ≃o n := order_iso_of_card_eq ncard.symm,
    let TV : T.inclusion V :=
    { to_fun := mn.to_rel_embedding.trans (nhead_mono.trans with_top.order_embedding),
      mat := λ i j, if some (sum.inr (mn i)) = j.map l.idx_fun then S.C else 0,
      scale := S.C,
      scale_C := rfl,
      ends := _,
      foo := λ j, j >>= λ j, (l.idx_fun j).elim (λ _, none) (some ∘ mn.symm),
      disj := _,
      mem := _, },
    work_on_goal 1 { intros i j hj,
      simp only [rel_embedding.coe_trans, rel_iso.to_rel_embedding_eq_coe, rel_iso.coe_coe_fn,
        function.comp_app],
      congr' 1,
      ext,
      cases j with j,
      { apply iff_of_false, apply option.some_ne_none, apply option.some_ne_none, },
      change some _ = some _ ↔ some _ = some _,
      rw [(option.some_injective _).eq_iff, (option.some_injective _).eq_iff],
      split,
      { intro h, apply le_antisymm, exact with_top.coe_le_coe.mp hj, apply finset.le_max',
        rw [finset.mem_filter], exact ⟨finset.mem_univ _, h.symm⟩, },
      { rintro rfl, symmetry, exact congr_fun nhead_idx_fun (mn i), }, },
    work_on_goal 1 { intros i j ij, apply if_neg,
      cases j with j,
      { apply option.some_ne_none, },
      refine mt _ ij,
      intro h,
      change sum.elim _ _ _ = some i,
      rw [option.map_some', (option.some_injective _).eq_iff] at h,
      rw ←h,
      change some _ = some _,
      rw mn.symm_apply_apply, },
    work_on_goal 1 { intros i j r hr,
      refine ⟨_, _, hr, _, rfl⟩,
      split_ifs, apply S.C_mem, apply S.zero_mem, },
    specialize h (co.restrict TV),
    obtain ⟨incT, kT, hT⟩ := h,

  }
end
