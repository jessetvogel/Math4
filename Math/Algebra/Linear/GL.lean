import Math.Algebra.Linear.Basic
import Math.Algebra.Module.Category
import Math.CategoryTheory.Aut
import Math.CategoryTheory.End

open CategoryTheory

namespace Algebra

variable (α : Type u) [Field α] (β : Type v) [V : VectorSpace α β]

def GL := Aut (Bundled.of β : Bundled (Module α))

instance : Group (GL α β) where
  mul := Iso.comp
  one := Iso.id _
  mul_one _ := by rfl
  one_mul _ := by rfl
  mul_assoc _ _ _ := by rfl
  inv := Iso.inverse
  mul_inv A := by {
    show Iso.comp A (Iso.inverse A) = Iso.id _;
    unfold Iso.comp;
    congr;
    exact A.comp_inv;
    exact A.comp_inv;
  }

-- instance GLGroup : Group (GL α β) := AutGroup (Bundled.of β V)
  
end Algebra
