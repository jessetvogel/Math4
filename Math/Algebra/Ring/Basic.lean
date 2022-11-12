import Math.Algebra.Monoid.Basic
import Math.Algebra.AddGroup.Basic
-- import Math.Algebra.Group.Basic

open Algebra.Monoid
open Algebra.AddMonoid
open Algebra.AddGroup

namespace Algebra

class Ring (α : Type u) extends AddGroup α, Monoid α where
  distrib_left : ∀ (x y z : α), x * (y + z) = x * y + x * z
  distrib_right : ∀ (x y z : α), (x + y) * z = x * z + y * z

attribute [simp] Ring.distrib_left Ring.distrib_right

namespace Ring

variable {α : Type u} [R : Ring α]

theorem cancel_add_left {x y z : α} (h : x + z = y + z) : x = y := by {
  have q : x + z + (-z) = y + z + (-z) := by rw [h];
  rw [← add_assoc, ← add_assoc, add_neg, add_zero, add_zero] at q;
  exact q;
}

theorem cancel_add_right {x y z : α} (h : z + x = z + y) : x = y := by {
  have q : (-z) + z + x = (-z) + z + y := by rw [← add_assoc, ← add_assoc, h];
  rw [neg_add, zero_add, zero_add] at q;
  exact q;
}

@[simp]
theorem mul_zero (x : α) : x * 0 = 0 := by {
  let q := distrib_left x 0 0;
  rw [zero_add] at q;
  have s : x * 0 + 0 = x * 0 + x * 0 := by rw [add_zero]; exact q;
  exact Eq.symm (cancel_add_right s);
}

@[simp]
theorem zero_mul (x : α) : 0 * x = 0 := by {
  let q := distrib_right 0 0 x;
  rw [add_zero] at q;
  have s : 0 * x + 0 = 0 * x + 0 * x := by rw [add_zero]; exact q;
  exact Eq.symm (cancel_add_right s);
}

instance : AddZero α where
  add_zero := R.add_zero
  zero_add := R.zero_add

instance : MulZero α where
  mul_zero := R.mul_zero
  zero_mul := R.zero_mul

end Ring

class abbrev RingHom (f : α → β) [Ring α] [Ring β] : Prop := AddGroupHom f, MulHom f, OneHom f

end Algebra
