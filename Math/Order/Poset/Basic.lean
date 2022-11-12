namespace Order

class Poset (α : Type _) extends LE α where
  refl : ∀ (x : α), x ≤ x
  asymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y
  trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z

end Order
