import Math.CategoryTheory.Basic

open CategoryTheory

namespace Algebra.Homological

-- Let's use cohomological indexing everywhere
structure Complex (α : Type _) [C : Category α] where
  X : Int → α
  d : ∀ (i : Int), C.hom (X i) (X (i + 1))
  d_comp_d : ∀ (i : Int), d (i + 1) ∘ d i = 0

end Algebra.Homological
