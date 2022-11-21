import Math.Order.Lattice.Basic

namespace Order

class HImp (α : Type _) where
  himp : α → α → α

infix:100 " ⇨ " => HImp.himp

class Heyting (α : Type _) extends Lattice α, HImp α where
  le_himp_iff : ∀ (x y z : α), x ⊓ y ≤ z ↔ x ≤ y ⇨ z

end Order
