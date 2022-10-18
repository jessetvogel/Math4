import Math.CategoryTheory.NatTrans

namespace CategoryTheory

open Category

structure Monad (α : Sort u) [C : Category α] where
  T : Functor α α
  μ : T.comp T ⇒ T
  η : Functor.id α ⇒ T
  assoc : ∀ (X : α), μ.app X ∘ T.map (μ.app X) = μ.app X ∘ μ.app (T.obj X)
  mul_one : ∀ (X : α), μ.app X ∘ η.app (T.obj X) = 𝟙 (T.obj X)
  one_mul : ∀ (X : α), μ.app X ∘ T.map (η.app X) = 𝟙 (T.obj X)

attribute [simp] Monad.assoc Monad.mul_one Monad.one_mul

namespace Monad

variable [Category α]

@[simp]
theorem μ_natural (M : Monad α) (f : hom X Y) : M.μ.app Y ∘ M.T.map (M.T.map f) = M.T.map f ∘ M.μ.app X := M.μ.natural f

end Monad

end CategoryTheory
