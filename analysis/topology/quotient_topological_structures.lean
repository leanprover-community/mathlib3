import analysis.topology.topological_structures
import group_theory.quotient_group

open function set

variables {α : Type*} [topological_space α] {β : Type*} [topological_space β]
variables {γ : Type*} [topological_space γ] {δ : Type*} [topological_space δ]

def is_open_map (f : α → β) := ∀ U : set α, is_open U → is_open (f '' U)

lemma is_open_map_iff_nhds_le (f : α → β) : is_open_map f ↔ ∀(a:α), nhds (f a) ≤ (nhds a).map f :=
begin
  split,
  { assume h a s hs,
    rcases mem_nhds_sets_iff.1 hs with ⟨t, hts, ht, hat⟩,
    exact filter.mem_sets_of_superset
      (mem_nhds_sets (h t ht) (mem_image_of_mem _ hat))
      (image_subset_iff.2 hts) },
  { refine assume h s hs, is_open_iff_mem_nhds.2 _,
    rintros b ⟨a, ha, rfl⟩,
    exact h _ (filter.image_mem_map $ mem_nhds_sets hs ha) }
end

namespace is_open_map

protected lemma id : is_open_map (@id α) := assume s hs, by rwa [image_id]

protected lemma comp
  {f : α → β} {g : β → γ} (hf : is_open_map f) (hg : is_open_map g) : is_open_map (g ∘ f) :=
by intros s hs; rw [image_comp]; exact hg _ (hf _ hs)

protected lemma prod {f : α → β} {g : γ → δ}
  (hf : is_open_map f) (hg : is_open_map g) : is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono ((is_open_map_iff_nhds_le f).1 hf a) ((is_open_map_iff_nhds_le g).1 hg b)
end

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_open_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ h s hs

lemma to_quotient_map {f : α → β}
  (open_map : is_open_map f) (cont : continuous f) (surj : surjective f) :
  quotient_map f :=
⟨ surj,
  begin
    ext s,
    show is_open s ↔ is_open (f ⁻¹' s),
    split,
    { exact cont s },
    { assume h,
      rw ← @image_preimage_eq _ _ _ s surj,
      exact open_map _ h }
  end⟩

end is_open_map

lemma is_open_coinduced {β} {s : set β} {f : α → β} :
  @is_open β (topological_space.coinduced f _inst_1) s ↔ is_open (f ⁻¹' s) :=
iff.refl _

section topological_group
variables [group α] [topological_group α]

@[to_additive is_open_map_add_left]
lemma is_open_map_mul_left (a : α) : is_open_map (λ x, x*a) :=
begin
  have : continuous (λ x, x*a⁻¹) := continuous_mul continuous_id continuous_const,
  apply is_open_map.of_inverse this;
    simp [function.right_inverse, function.left_inverse],
end

@[to_additive is_open_map_add_right]
lemma is_open_map_mul_right (a : α) : is_open_map (λ x, a*x) :=
begin
  have : continuous (λ x, a⁻¹*x) := continuous_mul continuous_const continuous_id,
  apply is_open_map.of_inverse this;
    simp [function.right_inverse, function.left_inverse],
end
end topological_group

section topological_group
variables [group α] [topological_group α] (N : set α) [normal_subgroup N]

@[to_additive quotient_add_group.quotient.topological_space]
instance : topological_space (quotient_group.quotient N) :=
by dunfold quotient_group.quotient; apply_instance

attribute [instance] quotient_add_group.quotient.topological_space

open quotient_group
@[to_additive quotient_add_group_saturate]
lemma quotient_group_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, y*x.1) '' s) :=
begin
  ext x,
  rw [mem_preimage_eq, mem_Union],
  split,
  { rintros ⟨a, a_in, h⟩,
    existsi [(⟨a⁻¹*x, quotient_group.eq.1 h⟩ : N), a, a_in],
    simp },
  { rintros ⟨⟨n, n_in⟩, ⟨a, a_in, rfl⟩⟩,
    existsi [a, a_in],
    rw quotient_group.eq,
    simp [n_in] }
end

@[to_additive quotient_add_group.open_coe]
lemma quotient_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_map_mul_left n s s_op
end

@[to_additive topological_add_group_quotient]
instance topological_group_quotient : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous.comp continuous_mul' continuous_quot_mk,

    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.to_quotient_map,
      { exact is_open_map.prod (quotient_group.open_coe N) (quotient_group.open_coe N) },
      { apply continuous.prod_mk,
        { exact continuous.comp continuous_fst continuous_quot_mk },
        { exact continuous.comp continuous_snd continuous_quot_mk } },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        existsi (x, y),
        refl }},
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), a⁻¹)),
    exact continuous.comp continuous_inv' continuous_quot_mk
  end }

attribute [instance] topological_add_group_quotient

end topological_group

section ideal_is_add_subgroup
variables [comm_ring α] {M : Type*} [module α M] (N : set α) [is_submodule N]

instance submodule_is_add_subgroup : is_add_subgroup N :=
{ zero_mem := is_submodule.zero,
  add_mem  := λ a b, is_submodule.add,
  neg_mem  := λ a, is_submodule.neg}

end ideal_is_add_subgroup

@[to_additive normal_add_subgroup_of_comm]
instance normal_subgroup_of_comm [comm_group α] (s : set α) [hs : is_subgroup s] :
  normal_subgroup s :=
{ normal := assume a hn b, by rwa [mul_comm b, mul_inv_cancel_right] }
attribute [instance] normal_add_subgroup_of_comm

section topological_ring
variables [comm_ring α] [topological_ring α] (N : set α) [is_ideal N]
open quotient_ring

instance topological_ring_quotient_topology : topological_space (quotient N) :=
by dunfold quotient_ring.quotient ; apply_instance

-- this should be quotient_add_saturate ...
lemma quotient_ring_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  rw mem_preimage_eq,
  rw mem_Union,
  split ; intro h,
  { rcases h with ⟨a, a_in, h⟩,
    rw [quotient_ring.eq, @is_ideal.neg_iff _ _ _ N _,
        show -(a-x) = -a + x, by {ring}] at h,
    existsi (⟨-a+x, h⟩ : N),
    rw mem_image,
    existsi [a, a_in],
    simp },
  { rcases h with ⟨⟨n, n_in⟩, x_in⟩,
    rw mem_image at x_in,
    rcases x_in with ⟨a, a_in, ha⟩,
    rw mem_image,
    existsi [a, a_in],
    rw quotient_ring.eq,
    rw @is_ideal.neg_iff _ _ _ N _,
    rwa show -(a - x) = n, by {rw ←ha, simp} }
end

lemma quotient_ring.is_open_map_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_ring_saturate N s,
  exact is_open_Union (assume ⟨n, _⟩, is_open_map_add_right n s s_op)
end

lemma quotient_ring.quotient_map : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))) :=
begin
  apply is_open_map.to_quotient_map,
  { exact is_open_map.prod (quotient_ring.is_open_map_coe N) (quotient_ring.is_open_map_coe N) },
  { apply continuous.prod_mk,
    { exact continuous.comp continuous_fst continuous_quot_mk },
    { exact continuous.comp continuous_snd continuous_quot_mk } },
  { rintro ⟨⟨x⟩, ⟨y⟩⟩,
    existsi (x, y),
    refl }
end

instance topological_ring_quotient : topological_ring (quotient N) :=
{ continuous_add :=
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst + p.snd)) :=
      continuous.comp continuous_add' continuous_quot_mk,
    (quotient_map.continuous_iff (quotient_ring.quotient_map N)).2 cont,
  continuous_neg := continuous_quotient_lift _ (continuous.comp continuous_neg' continuous_quot_mk),
  continuous_mul :=
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous.comp continuous_mul' continuous_quot_mk,
    (quotient_map.continuous_iff (quotient_ring.quotient_map N)).2 cont }

end topological_ring
