import Math.Algebra.Basic

namespace Algebra

class Monoid (α : Type u) extends Mul α, One α, MulOne α where
  mul_assoc : ∀ (x y z : α), x * (y * z) = (x * y) * z

attribute [simp] Monoid.mul_assoc Monoid.mul_one Monoid.one_mul

namespace Monoid

variable [Monoid α]

def npow (x : α) (n : Nat) : α := match n with
| Nat.zero => 1
| Nat.succ n => x * (npow x n)

instance : Pow α Nat where pow := npow

@[simp] theorem npow_zero (x : α) : x ^ (0 : Nat) = 1 := by rfl;
@[simp] theorem npow_succ (x : α) (n : Nat) : x ^ n.succ = x * x ^ n := by rfl;
@[simp] theorem npow_one (x : α) : x ^ (1 : Nat) = x := by have q := npow_succ x 0; rw [npow_zero, mul_one] at q; exact q;
@[simp] theorem npow_mul (x : α) (m n : Nat) : x ^ (n + m) = x ^ n * x ^ m := by {
  induction n with
  | zero => simp
  | succ n hn => simp [Nat.succ_add, hn];
}

theorem left_inv_eq_right_inv {x y z : α} (h₁ : x * y = 1) (h₂ : y * z = 1) : x = z :=
  by rw [← mul_one x, ← h₂, mul_assoc, h₁, one_mul]

end Monoid

class abbrev MonoidHom (f : α → β) [Monoid α] [Monoid β] : Prop := MulHom f, OneHom f

-- Very good!
-- variable (g : β → γ) (f : α → β) [Monoid α] [Monoid β] [Monoid γ] [MonoidHom f] [MonoidHom g]
-- #check (inferInstance : MonoidHom (id : α → α))
-- #check (inferInstance :  MonoidHom (g ∘ f))

end Algebra
