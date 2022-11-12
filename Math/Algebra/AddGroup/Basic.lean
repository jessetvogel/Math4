import Math.Algebra.AddMonoid.Basic

open Algebra.AddMonoid

namespace Algebra

class AddGroup (α : Type u) extends AddMonoid α, Neg α where
  add_neg : ∀ (x : α), x + (-x) = 0

namespace AddGroup

variable [AddGroup α]

def neg_add (x : α) : (-x) + x = 0 := by rw [add_comm, add_neg];

end AddGroup

class abbrev AddGroupHom (f : α → β) [AddGroup α] [AddGroup β] : Prop := AddHom f

end Algebra
