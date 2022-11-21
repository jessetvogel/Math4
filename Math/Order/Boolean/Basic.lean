import Math.Order.Lattice.Basic
import Math.Order.Bounded.Basic

namespace Order

class Boolean (α : Type _) extends Lattice α, Compl α, Bounded α where
  sup_compl : ∀ (x : α), x ⊔ xᶜ = ⊤
  inf_compl : ∀ (x : α), x ⊓ xᶜ = ⊥
  
end Order
