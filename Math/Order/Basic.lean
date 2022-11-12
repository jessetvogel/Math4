namespace Order

class LUB (α : Type _) where
  lub : α → α → α

infixl:80 " ⊔ " => LUB.lub

class GLB (α : Type _) where
  glb : α → α → α

infixl:80 " ⊓ " => GLB.glb

end Order
