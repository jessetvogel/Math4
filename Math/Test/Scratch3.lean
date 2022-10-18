namespace Test

structure Set where
  set : Type u

structure Mul extends Set where
  mul : set → set → set

structure Add extends Set where
  add : set → set → set

infixl:80 " * " => Mul.mul _
infixl:60 " + " => Add.add _

@[appUnexpander Mul.mul]
def unexpandMul : Lean.PrettyPrinter.Unexpander
| `(Mul.mul $_ $x $y) => `($x * $y)
| _ => throw ()

@[appUnexpander Add.add]
def unexpandAdd : Lean.PrettyPrinter.Unexpander
| `(Add.add $_ $x $y) => `($x + $y)
| _ => throw ()

structure MulAdd extends Mul, Add

unif_hint (a : Add) (ma : MulAdd) where
  a =?= MulAdd.toAdd ma ⊢ Add.toSet a =?= Mul.toSet (MulAdd.toMul ma)

-- Bad: types of `x * y` and `x + y` do not match
example (X : MulAdd) (x y : X.set) : x * y = x + y := by {

}
-- Good: in this case they do match
example (X : MulAdd) (x y : X.set) : X.mul x y = X.add x y := by sorry

-- Bad: fails for the same reason as above
example (X : MulAdd) (x y : X.set) : X.mul x y = Add.add _ x y := by sorry
-- Good: this works, apparently because of the order "Mul, Add" as opposed to "Add, Mul"
example (X : MulAdd) (x y : X.set) : Mul.mul _ x y = X.add x y := by sorry


end Test

/-

Diamond problem with notation

Consider the structures as in the code below. The examples labeled 'bad' do not work because the types `x * y` and `x + y` do not match. I know I could use typeclasses, e.g. `class MulInv (α : Type u) extends Mul α, Inv α`, but this is not what I want to do. Why can't Lean see these types are the same? Is there any way to get this 'diamond problem' to work well with the custom notation?

-/