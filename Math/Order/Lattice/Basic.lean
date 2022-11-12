import Math.Order.Basic
import Math.Order.Poset.Basic

namespace Order

class Lattice (α : Type _) extends Poset α, LUB α, GLB α where
  le_lub_left : ∀ (x y : α), x ≤ x ⊔ y
  le_lub_right : ∀ (x y : α), y ≤ x ⊔ y
  lub_le : ∀ {x y z : α}, x ≤ z → y ≤ z → x ⊔ y ≤ z
  glb_le_left : ∀ (x y : α), x ⊓ y ≤ x
  glb_le_right : ∀ (x y : α), x ⊓ y ≤ y
  le_glb : ∀ {x y z : α}, x ≤ y → x ≤ z → x ≤ y ⊓ z

end Order
