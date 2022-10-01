namespace Data

structure Equiv (α : Sort u) (β : Sort v) where
  to        : α → β
  inv       : β → α
  left_inv  : ∀ x, inv (to x) = x
  right_inv : ∀ x, to (inv x) = x

infix:80 " ≃ " => Equiv

attribute [simp] Equiv.left_inv
attribute [simp] Equiv.right_inv

end Data
