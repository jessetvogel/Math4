import Math.CategoryTheory.NatTrans

namespace CategoryTheory

variable (α : Sort u) (β : Sort v) [Category α] [Category β]

structure Equivalence where
  F : Functor α β
  G : Functor β α
  μ : NatIso (Functor.id α) (G.comp F)
  ν : NatIso (Functor.id β) (F.comp G)

end CategoryTheory
