import Math.Algebra.AddMonoid.Basic

open Algebra.AddMonoid

namespace Algebra

class Abelian (α : Type u) extends AddMonoid α, Neg α where
  add_neg : ∀ (x : α), x + (-x) = 0

-- instance [Abelian α] : Sub α where 
  -- sub := λ x y => x + (-y)

namespace Abelian

variable [Abelian α]

def neg_add (x : α) : (-x) + x = 0 := by rw [add_comm, add_neg];

end Abelian

end Algebra
