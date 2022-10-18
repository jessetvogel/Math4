namespace Algebra

structure Carrier where
  set : Type u

structure Mul extends Carrier where
  mul : set → set → set

infixl:100 " * " => Mul.mul _

@[appUnexpander Mul.mul]
def unexpandMul : Lean.PrettyPrinter.Unexpander
| `(Mul.mul $_ $x $y) => `($x * $y)
| _ => throw ()

structure Semigroup extends Mul where
  mul_assoc (a b c : set) : (a * b) * c = a * (b * c)

#check Semigroup.mul_assoc

structure CommSemigroup extends Semigroup where
  mul_comm (a b : set) : a * b = b * a

class One extends Carrier where
  one : set

structure Monoid extends Semigroup, One where
  one_mul (a : set) : one * a = a
  mul_one (a : set) : a * one = a

class CommMonoid extends Monoid, CommSemigroup

-- set_option pp.all true
#check @CommMonoid.mk
#print CommMonoid.toCommSemigroup

structure Inv extends Carrier where
  inv : set → set

postfix:100 "⁻¹" => Inv.inv _

@[appUnexpander Inv.inv]
def unexpandInv : Lean.PrettyPrinter.Unexpander
| `(Inv.inv $_ $x) => `($x⁻¹)
| _ => throw ()

structure Group extends Inv, Monoid where
  mul_left_inv (a : set) : mul (inv a) a = one

class CommGroup extends Group, CommMonoid

#check @CommGroup.mk
#print CommGroup.toCommMonoid

def eq_of_mul_left (G : Group) (x : G.set) {y z : G.set} (h : y = z) : x * y = x * z := by {
  rw [h];
}

def cancel_left {G : Group} (x : G.set) {y z : G.set} (h : x * y = x * z) : y = z := by {
  have q := eq_of_mul_left G (x⁻¹) h;
  simp at q;
  exact q;
}


-- class AddSemigroup extends Add where
--   add_assoc (a b c : α) : a + b + c = a + (b + c)

-- class AddCommSemigroup (α : Type u) extends AddSemigroup α where
--   add_comm (a b : α) : a + b = b + a

-- class Zero (α : Type u) where
--   zero : α

-- instance [Zero α] : OfNat α (nat_lit 0) where
--   ofNat := Zero.zero

-- class AddMonoid (α : Type u) extends AddSemigroup α, Zero α where
--   zero_add (a : α) : 0 + a = a
--   add_zero (a : α) : a + 0 = a

-- class AddCommMonoid (α : Type u) extends AddMonoid α, AddCommSemigroup α

-- class AddGroup (α : Type u) extends AddMonoid α, Neg α where
--   add_left_neg (a : α) : -a + a = 0

-- class AddCommGroup (α : Type u) extends AddGroup α, AddCommMonoid α

-- class Distrib (α : Type u) extends Mul α, Add α where
--   left_distrib ( a b c : α) : a * (b + c) = (a * b) + (a * c)
--   right_distrib (a b c : α) : (a + b) * c = (a * c) + (b * c)

-- class MulZero (α : Type u) extends Mul α, Zero α where
--   zero_mul (a : α) : 0 * a = 0
--   mul_zero (a : α) : a * 0 = 0

-- class ZeroNeOne (α : Type u) extends Zero α, One α where
--   zero_ne_one : (0:α) ≠ 1

-- class Semiring (α : Type u) extends AddCommMonoid α, Monoid α, Distrib α, MulZero α

-- class CommSemiring (α : Type u) extends Semiring α, CommMonoid α

-- class Ring (α : Type u) extends AddCommGroup α, Monoid α, Distrib α

-- class CommRing (α : Type u) extends Ring α, CommSemigroup α

-- class NoZeroDivisors (α : Type u) extends Mul α, Zero α where
--   eq_zero_or_eq_zero_of_mul_eq_zero (a b : α) : a * b = 0 → a = 0 ∨ b = 0

-- class IntegralDomain (α : Type u) extends CommRing α, NoZeroDivisors α, ZeroNeOne α

-- class DivisionRing (α : Type u) extends Ring α, Inv α, ZeroNeOne α where
--   mul_inv_cancel {a : α} : a ≠ 0 → a * a⁻¹ = 1
--   inv_mul_cancel {a : α} : a ≠ 0 → a⁻¹ * a = 1

-- class Field (α : Type u) extends DivisionRing α, CommRing α

-- set_option pp.all false in
-- #check @Field.mk
-- #print Field.toDivisionRing
-- #print Field.toCommRing

end Algebra
