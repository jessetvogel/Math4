import Math.Order.Lattice.Basic

namespace Order.Lattice

def dual (α : Type _) [Lattice α] := α

variable [L : Lattice α]

instance : Lattice (dual α) where
  le x y := L.le y x
  refl := L.refl
  asymm h₁ h₂ := L.asymm h₂ h₁
  trans h₁ h₂ := L.trans h₂ h₁
  sup := L.inf
  inf := L.sup
  le_sup_left := L.inf_le_left
  le_sup_right := L.inf_le_right
  sup_le := L.le_inf
  inf_le_left := L.le_sup_left
  inf_le_right := L.le_sup_right
  le_inf := L.sup_le

end Order.Lattice
