import linear_algebra.free_module linear_algebra.basis linear_algebra.direct_sum.finsupp m4r.koszul_of_free m4r.exterior_power
universes u w v
noncomputable theory
open_locale classical
variables {R : Type u} [comm_ring R] {M : Type u} [add_comm_group M] [module R M]
  {ι : Type w}

def fin_add_equiv (i j : ℕ) :
  ((fin i → ι) × (fin j → ι)) ≃ (fin (i + j) → ι) :=
{ to_fun := λ f, fin.append rfl f.1 f.2,
  inv_fun := λ f, (f ∘ fin.cast_add j, f ∘ @fin.nat_add i j),
  left_inv := λ x,
    begin
      ext k,
      { convert fin.append_apply_fst' x.1 x.2 rfl k },
      { ext k,
        convert fin.append_apply_snd' x.1 x.2 rfl _ },
    end,
  right_inv := λ x,
    begin
      ext k,
      dsimp,
      cases classical.em ((k : ℕ) < i),
      { rw [fin.append_apply_fst _ _ _ _ h, function.comp_app],
        congr,
        ext,
        refl, },
      { rw [fin.append_apply_snd _ _ _ _ h, function.comp_app],
        congr,
        ext,
        simp only [fin.coe_nat_add, fin.coe_mk],
        rw nat.add_sub_cancel' (not_lt.1 h), }
    end }

lemma is_basis.tensor_power {b : ι → M} (hb : is_basis R b) (n : ℕ) :
  is_basis R (λ (i : fin n → ι), tpow.mk R M n (b ∘ i)) :=
begin
  induction n with n hn,
  { split,
    { rw linear_independent_iff,
      intros l hl,
      rw finsupp.total_unique at hl,
      unfold tpow.mk at hl,
      rw [algebra.id.smul_eq_mul, mul_one] at hl,
      ext,
      rw [subsingleton.elim a (default _), hl],
      refl },
    { convert ideal.span_singleton_one,
      rw set.range_unique,
      refl, }},
  { convert @is_basis.comp ((fin n → ι) × (fin 1 → ι)) (fin n.succ → ι) _ _ _ _ _ _
      (finsupp.is_basis.tensor_product hn (is_basis.comp hb (equiv.fun_unique (fin 1) ι)
        (equiv.bijective _))) (fin_add_equiv n 1).symm (equiv.bijective _),
    ext,
    unfold tpow.mk,
    simp only [tensor_product.mk_apply, fin.default_eq_zero,
      equiv.fun_unique_apply, function.comp_app],
    congr,
    ext,
    simp only [add_zero, fin.coe_zero, fin.coe_nat_fin_succ, fin.coe_nat_add], },
end

variables (R)
lemma is_basis_single_one' (n : ℕ) :
  @is_basis (fin n) R (fin n → R) (λ i, (finsupp.single i (1 : R) : fin n → R)) _ _ _ :=
begin
  convert linear_equiv.is_basis finsupp.is_basis_single_one
  (is_basis.equiv_fun $ @finsupp.is_basis_single_one R (fin n) _),
  ext i j,
  simp only [is_basis.equiv_fun_self, function.comp_app],
  refl,
end

def exists_same2 (n i : ℕ) : set (fin i → fin n) :=
{ v | ∃ (j k : fin i) (h : v j = v k), j ≠ k }

lemma exists_same2_mem (n i : ℕ) (v : exists_same2 n i) :
  (λ j, function.update 0 j 1) ∘ v.1 ∈ tuple.exists_same (fin n → R) i :=
begin
  rcases v.2 with ⟨j, k, hv, hjk⟩,
  refine ⟨j, k, _, hjk⟩,
  dsimp,
  congr,
  exact hv,
end

lemma exists_same2_span_disjoint (n i : ℕ) :
  disjoint (submodule.span R ((λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) '' (exists_same2 n i)))
    (submodule.span R ((λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) '' (exists_same2 n i)ᶜ)) :=
linear_independent.disjoint_span_image (is_basis.tensor_power (is_basis_single_one' R n) i).1
  (le_bot_iff.2 (set.inter_compl_self _))

variables [nontrivial R]
noncomputable def multiply_repr : Π (i n : ℕ),
  (fin i → fin n → R) → ((fin i → fin n) →₀ R)
| 0 n y :=
  { support := {default _},
    to_fun := λ z, 1,
    mem_support_to_fun := λ f, ⟨λ h, one_ne_zero,
      λ h, finset.mem_singleton.2 (subsingleton.elim _ _)⟩ }
| (i+1) n y :=
  { support := set.to_finset {f : fin (i + 1) → fin n | y 0 (f 0) * multiply_repr i n
      (fin.tail y) (fin.tail f) ≠ 0},
    to_fun := λ f, y 0 (f 0) * multiply_repr i n (fin.tail y) (fin.tail f),
    mem_support_to_fun := λ x, by simp }

lemma tpow_repr_eq (n i : ℕ) (z : fin i → fin n → R) :
  (is_basis.tensor_power (is_basis_single_one' R n) i).repr
    (tpow.mk R (fin n → R) i z) =
  multiply_repr R i n z :=
begin
  induction i with i hi,
  { unfold multiply_repr tpow.mk,
    ext,
    simp only [finsupp.coe_mk],
    rw [subsingleton.elim a (default _),
        @is_basis.repr_eq_single _ _ _ _ _ _ _ _ (default _), finsupp.single_eq_same] },
  { unfold multiply_repr tpow.mk,
    have := hi (fin.init z),
    ext,
    sorry },

end


lemma multiply_repr_of_exists_same2 (n i : ℕ) (z : fin i → fin n → R)
  {j k : fin i} (hz : z j = z k) (hjk : j ≠ k)
  (x : fin i → fin n) (hx : x ∈ (multiply_repr R i n z).support) :
  x j = x k :=
sorry

lemma tpow_exists_same2 (n i : ℕ) :
  submodule.span R ((λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) '' (exists_same2 n i)) =
  epow_ker R (fin n → R) i :=
begin
  refine le_antisymm _ _,
  { refine submodule.span_mono _,
    rintro x ⟨y, ⟨j, k, hy, hjk⟩, hx⟩,
    exact ⟨(λ J, finsupp.single (y J) (1 : R)), ⟨j, k, by dsimp; rw hy, hjk⟩, hx⟩ },
  { refine submodule.span_le.2 _,
    rintros x ⟨y, ⟨j, k, hy, hjk⟩, hx⟩,
    sorry },
end

lemma tpow_exists_same2_compl (n i : ℕ) :
  submodule.span R ((λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) '' (exists_same2 n i)ᶜ) =
  submodule.span R (tpow.mk R (fin n → R) i '' (tuple.exists_same (fin n → R) i)ᶜ) :=
sorry

lemma disjoint_epow_ker_compl (n i : ℕ) :
  disjoint (epow_ker R (fin n → R) i)
  (submodule.span R
    (tpow.mk R (fin n → R) i '' (tuple.exists_same (fin n → R) i)ᶜ)) :=
begin
  have := @linear_independent.disjoint_span_image (fin i → fin n) R
    (tpow R (fin n → R) i) (λ (j : fin i → fin n), tpow.mk R (fin n → R) i
      ((λ (i : fin n), (finsupp.single i 1 : fin n → R)) ∘ j)) _ _ _
    (is_basis.tensor_power (is_basis_single_one' R n) i).1
    (exists_same2 n i) (exists_same2 n i)ᶜ
    (le_bot_iff.2 (set.inter_compl_self _)),
  rwa [tpow_exists_same2_compl, tpow_exists_same2] at this,
end

def aux_fun (n i : ℕ) : (exists_same2 n i)ᶜ → tpow R (fin n → R) i :=
(λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) ∘ subtype.val

lemma lemma_i_actually_want (n i : ℕ) :
  disjoint (submodule.span R (set.range (aux_fun R n i))) (epow_ker R (fin n → R) i) :=
begin
  rw ←tpow_exists_same2 R n i,
  have := @linear_independent.disjoint_span_image (fin i → fin n) R
    (tpow R (fin n → R) i) (λ (j : fin i → fin n), tpow.mk R (fin n → R) i
      ((λ (i : fin n), (finsupp.single i 1 : fin n → R)) ∘ j)) _ _ _
    (is_basis.tensor_power (is_basis_single_one' R n) i).1
    (exists_same2 n i) (exists_same2 n i)ᶜ
    (le_bot_iff.2 (set.inter_compl_self _)),
  rw disjoint.comm at this,
  convert this,
  exact (set.image_eq_range _ _).symm,
end

def epow.to_basis (n i : ℕ) (l : list (fin n)) (hli : l.length = i) :=
epow.mk R (fin n → R) i (λ j, finsupp.single (l.nth_le j (hli.symm ▸ j.2)) (1 : R))

def epow.basis (n i : ℕ) (j : fin (n.choose i)) : epow R (fin n → R) i :=
epow.to_basis R n i ((list.sublists_len i (list.fin_range n)).nth_le j
    (by rw [list.length_sublists_len, list.length_fin_range]; exact j.2))
    (list.length_of_sublists_len (list.nth_le_mem _ _ _))

lemma nth_le_inj_of_mem_sublists_fin_range (n i : ℕ) (l : list (fin n))
  (h : l ∈ (list.fin_range n).sublists_len i) :
  function.injective (λ j : fin i, list.nth_le l j ((list.length_of_sublists_len h).symm ▸ j.2)) :=
λ x y hxy, fin.ext (list.nodup_iff_nth_le_inj.1 (list.nodup_of_sublist (list.mem_sublists_len.1 h).1
(list.nodup_fin_range n)) x y (by rw (list.mem_sublists_len.1 h).2; exact x.2)
  (by rw (list.mem_sublists_len.1 h).2; exact y.2) hxy)

lemma not_mem_exists_same_of_mem_sublists_len [nontrivial R] (n i : ℕ) (l : list (fin n))
  (h : l ∈ list.sublists_len i (list.fin_range n)) :
  (λ j : fin i, (finsupp.single (l.nth_le j ((list.length_of_sublists_len h).symm ▸ j.2)) 1 : fin n → R))
    ∉ tuple.exists_same (fin n → R) i :=
begin
  rintro ⟨j, k, hf, hjk⟩,
  dsimp at hf,
  refine @one_ne_zero R _ _ _,
  have := finsupp.ext_iff.1 (finsupp.coe_fn_injective hf) (l.nth_le j
    ((list.length_of_sublists_len h).symm ▸ j.2)),
  rw finsupp.single_eq_same at this,
  rw this,
  convert finsupp.single_eq_of_ne _,
  exact (λ hl, hjk (nth_le_inj_of_mem_sublists_fin_range n i l h hl.symm)),
end

theorem epow_eq_zero_iff (n i : ℕ) (f : fin i → fin n) :
  epow.mk R (fin n → R) i (λ j, function.update 0 (f j) 1) = 0 ↔
  (λ j, function.update 0 (f j) 1) ∈ tuple.exists_same (fin n → R) i :=
begin
  sorry
end
variables (n i : ℕ) (j : fin (n.choose i))

theorem jfc {M : Type u} [add_comm_group M] [module R M] {ι : Type w}
  (v : ι → M) (s : set ι) (h : linear_independent R v) :
  linear_independent R (v ∘ subtype.val : s → M) :=
 linear_independent.comp h _ subtype.val_injective

#check vector.nth_of_fn

lemma list.sublists_len_nodup {α : Type w} (l : list α) (h : l.nodup) (i : ℕ) :
  (l.sublists_len i).nodup := sorry

def to_exists_same2_aux (n i : ℕ) (j : fin (n.choose i)) : fin i → fin n :=
vector.nth (subtype.mk ((list.sublists_len i (list.fin_range n)).nth_le j
    (by rw [list.length_sublists_len, list.length_fin_range]; exact j.2))
(list.mem_sublists_len.1 (list.nth_le_mem (list.sublists_len i (list.fin_range n)) j _)).2)

lemma to_exists_same2_cond (n i : ℕ) (j : fin (n.choose i)) :
  to_exists_same2_aux n i j ∈ (exists_same2 n i)ᶜ := λ ⟨k, l, hj, hkl⟩,
begin
  unfold to_exists_same2_aux at hj,
  rw vector.nth_eq_nth_le at hj,
  contrapose! hkl,
  exact nth_le_inj_of_mem_sublists_fin_range n i ((list.sublists_len i (list.fin_range n)).nth_le j _)
    (list.nth_le_mem _ j _) hj,
end

def to_exists_same2 (n i : ℕ) (j : fin (n.choose i)) :
  ((exists_same2 n i)ᶜ : set _) :=
⟨to_exists_same2_aux n i j, to_exists_same2_cond n i j⟩

def exists_same2_compl_copy (n i : ℕ) : set (fin i → fin n) :=
vector.nth '' (set.range (λ (v : (((list.sublists_len i (list.fin_range n)).to_finset)
  : set (list (fin n)))), subtype.mk v.1 (list.mem_sublists_len.1 (
begin
  show v.1 ∈ list.sublists_len i (list.fin_range n),
  convert v.2,
  exact (list.erase_dup_eq_self.2 ((list.fin_range n).sublists_len_nodup (list.nodup_fin_range n) i)).symm
end)).2))

lemma sublists_len_to_finset (n i : ℕ) :
  exists_same2_compl_copy n i = (exists_same2 n i)ᶜ :=
sorry

lemma sublists_surj (n i : ℕ) (j : (exists_same2 n i)ᶜ) :
  ∃! (l : fin (n.choose i)), to_exists_same2 n i l = j := sorry

def sublists_equiv (n i : ℕ) : fin (n.choose i) ≃ ((exists_same2 n i)ᶜ :
  set (fin i → fin n)) :=
{ to_fun := λ j, ⟨to_exists_same2_aux n i j, to_exists_same2_cond n i j⟩,
  inv_fun := λ j, classical.some (sublists_surj n i j),
  left_inv := sorry,
  right_inv := sorry }

theorem epow.basis_li (n i : ℕ) : linear_independent R (epow.basis R n i) :=
begin
  have := jfc R (λ (j : fin i → fin n), tpow.mk R (fin n → R) i
    (λ (k : fin i), (finsupp.single (j k) 1 : fin n → R))) (exists_same2 n i)ᶜ
    (is_basis.tensor_power (is_basis_single_one' R n) i).1,
  have hhh := lemma_i_actually_want R n i,
  rw ←(epow_ker R (fin n → R) i).ker_mkq at hhh,
  have := linear_independent.map this hhh,
  refine (linear_independent_equiv' (sublists_equiv n i).symm _).1 this,
  sorry
end

lemma set.range_eq_of_comp_equiv {α : Type u} {β : Type w} {γ : Type v} (f : α ≃ β)
  (g : β → γ) : set.range g = set.range (g ∘ f) :=
begin
  ext,
  split,
  { rintro ⟨y, hy⟩,
    exact ⟨f.symm y, by simpa using hy⟩},
  { rintro ⟨y, hy⟩,
    exact ⟨f y, hy⟩ }
end

theorem epow.basis_span (n i : ℕ) : submodule.span R (set.range $ epow.basis R n i) = ⊤ :=
begin
  have : submodule.span R (set.range $ epow.basis R n i) =
    (submodule.span R (set.range (aux_fun R n i))).map (epow_ker R (fin n → R) i).mkq :=
  begin
    rw ←submodule.span_image,
    congr,
    rw [←set.range_comp, set.range_eq_of_comp_equiv (sublists_equiv n i)],
    congr,
  end,
  rw [this, submodule.map_mkq_eq_top, ←tpow_exists_same2 R n i, ←submodule.span_union],
  convert (is_basis.tensor_power (is_basis_single_one' R n) i).2,
  unfold aux_fun,
  erw ←set.image_eq_range,
  rw [←set.image_union, ←set.image_univ],
  congr,
  rw set.union_compl_self,
end

lemma epow.is_basis (n i : ℕ) : is_basis R (epow.basis R n i) :=
⟨epow.basis_li R n i, epow.basis_span R n i⟩

def epow.equiv_choose (n i : ℕ) : epow R (fin n → R) i ≃ₗ[R] (fin (n.choose i) → R) :=
is_basis.equiv_fun (epow.is_basis R n i)

def epow.equiv_succ (n i : ℕ) :
  epow R (fin n.succ → R) i.succ ≃ₗ[R] epow R (fin n → R) i × epow R (fin n → R) i.succ :=
(epow.equiv_choose R n.succ i.succ).trans $ (rk_free_prod_eq_add R (n.choose i) (n.choose i.succ)).symm.trans
  (linear_equiv.prod (epow.equiv_choose R n i).symm (epow.equiv_choose R n i.succ).symm)

def Koszul_isom_free_Koszul (n : ℕ) (x : fin n.succ → R) :
  Koszul R (fin n.succ → R) x ≅ free_Koszul R n x :=
{ hom :=
  { f := λ i, int.rec_on i
      (λ i, ((epow.equiv_choose R n.succ i).trans
        (free_Koszul_isom_choose R i x).to_linear_equiv.symm).to_linear_map) 0,
    comm' :=
  begin
    ext i y,
    induction i with i i,
    { simp only [category_theory.iso.to_linear_equiv_symm_apply, linear_equiv.trans_apply,
        to_linear_map_apply, function.comp_app, category_theory.pi.comp_apply, Module.coe_comp],
      induction i with i hi,
      { sorry },
      { sorry } },
    { simp only [function.comp_app, category_theory.pi.comp_apply,
        category_theory.graded_object.zero_apply, Module.coe_comp, category_theory.limits.zero_comp,
        linear_map.zero_apply],
      exact (linear_map.map_zero _) },
  end },
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
