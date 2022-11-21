import Math.Order.Basic

namespace Order

class Bounded (α : Type _) extends LE α, Top α, Bot α where
  le_top : ∀ (x : α), x ≤ ⊤
  bot_le : ∀ (x : α), ⊥ ≤ x
  
end Order
