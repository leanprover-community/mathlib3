import tactic.transport_2
import algebra.lie_algebra

def lie_ring.map {α : Type} [lie_ring α] {β : Type} (e : α ≃ β) : lie_ring β :=
by transport.
