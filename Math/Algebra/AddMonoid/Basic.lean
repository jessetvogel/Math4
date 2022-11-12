import Math.Algebra.Basic

namespace Algebra

class AddMonoid (α : Type u) extends Add α, Zero α where
  add_assoc : ∀ (x y z : α), x + (y + z) = (x + y) + z
  add_comm : ∀ (x y : α), x + y = y + x
  add_zero : ∀ (x : α), x + 0 = x

namespace AddMonoid

variable [AddMonoid α]

def zero_add : ∀ (x : α), 0 + x = x := λ _ => by rw [add_comm, add_zero];

end AddMonoid

class abbrev AddMonoidHom (f : α → β) [AddMonoid α] [AddMonoid β] : Prop := AddHom f, ZeroHom f

end Algebra
