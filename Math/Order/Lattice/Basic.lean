import Math.Order.Basic
import Math.Order.Poset.Basic
import Math.Order.Bounded.Basic

namespace Order

variable (α : Type _)

class SupSemilattice extends Poset α, Sup α where
  le_sup_left : ∀ (x y : α), x ≤ x ⊔ y
  le_sup_right : ∀ (x y : α), y ≤ x ⊔ y
  sup_le : ∀ {x y z : α}, x ≤ z → y ≤ z → x ⊔ y ≤ z

class InfSemilattice extends Poset α, Inf α where
  inf_le_left : ∀ (x y : α), x ⊓ y ≤ x
  inf_le_right : ∀ (x y : α), x ⊓ y ≤ y
  le_inf : ∀ {x y z : α}, x ≤ y → x ≤ z → x ≤ y ⊓ z

class abbrev Lattice := SupSemilattice α, InfSemilattice α

end Order
