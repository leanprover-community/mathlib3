import ring_theory.dedekind_domain.ideal
import ring_theory.chain_of_divisors

@[simps]
def ideal_correspondence (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient):
  {p : ideal T | p ∣ I} ≃ {p : ideal S | p ∣ J} :=
{
  to_fun := λ X, ⟨comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)),
    begin
      rw [set.mem_set_of_eq, dvd_iff_le],
      have : (J^.quotient.mk).ker ≤ comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)),
      { exact ker_le_comap J^.quotient.mk },
      rw mk_ker at this,
      exact this,
    end ⟩,
  inv_fun := λ X, ⟨comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)),
    begin
      rw [set.mem_set_of_eq, dvd_iff_le],
      have : (I^.quotient.mk).ker ≤ comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)),
      { exact ker_le_comap I^.quotient.mk },
      rw mk_ker at this,
      exact this,
    end⟩,
  left_inv := λ X,
  begin
    obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective, map_of_equiv _ f, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 hp,
  end,
  right_inv := λ X,
    begin
      obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective],
      nth_rewrite 0 ← ring_equiv.symm_symm f,
      rw [map_of_equiv _ f.symm, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 hp,
    end
}
