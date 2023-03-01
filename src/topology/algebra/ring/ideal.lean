import topology.algebra.ring.basic
import ring_theory.ideal.quotient
/-!
- `ideal.closure`: The closure of an ideal is an ideal.
- `topological_ring_quotient`: The quotient of a topological semiring by an ideal is a
  topological ring.

-/
section topological_ring
variables {α : Type*} [topological_space α] [ring α] [topological_ring α]

/-- The closure of an ideal in a topological ring as an ideal. -/
def ideal.closure (S : ideal α) : ideal α :=
{ carrier   := closure S,
  smul_mem' := λ c x hx, map_mem_closure (mul_left_continuous _) hx $ λ a, S.mul_mem_left c,
  ..(add_submonoid.topological_closure S.to_add_submonoid) }

@[simp] lemma ideal.coe_closure (S : ideal α) : (S.closure : set α) = closure S := rfl

@[simp] lemma ideal.closure_eq_of_is_closed (S : ideal α) [hS : is_closed (S : set α)] :
  S.closure = S :=
ideal.ext $ set.ext_iff.mp hS.closure_eq

end topological_ring

section topological_ring
variables {α : Type*} [topological_space α] [comm_ring α] (N : ideal α)
open ideal.quotient

instance topological_ring_quotient_topology : topological_space (α ⧸ N) :=
show topological_space (quotient _), by apply_instance

-- note for the reader: in the following, `mk` is `ideal.quotient.mk`, the canonical map `R → R/I`.

variable [topological_ring α]

lemma quotient_ring.is_open_map_coe : is_open_map (mk N) :=
begin
  intros s s_op,
  change is_open (mk N ⁻¹' (mk N '' s)),
  rw quotient_ring_saturate,
  exact is_open_Union (λ ⟨n, _⟩, is_open_map_add_left n s s_op)
end

lemma quotient_ring.quotient_map_coe_coe : quotient_map (λ p : α × α, (mk N p.1, mk N p.2)) :=
is_open_map.to_quotient_map
((quotient_ring.is_open_map_coe N).prod (quotient_ring.is_open_map_coe N))
((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
(by rintro ⟨⟨x⟩, ⟨y⟩⟩; exact ⟨(x, y), rfl⟩)

instance topological_ring_quotient : topological_ring (α ⧸ N) :=
topological_semiring.to_topological_ring
{ continuous_add :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst + p.snd)) :=
      continuous_quot_mk.comp continuous_add,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont,
  continuous_mul :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont }

end topological_ring

