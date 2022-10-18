namespace Data

structure Equiv (α : Sort u) (β : Sort v) where
  map : α → β
  inv : β → α
  inv_map : ∀ x, inv (map x) = x := by simp
  map_inv : ∀ x, map (inv x) = x := by simp

infix:80 " ≃ " => Equiv

attribute [simp] Equiv.inv_map Equiv.map_inv

end Data
