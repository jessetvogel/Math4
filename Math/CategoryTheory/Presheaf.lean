import Math.CategoryTheory.Functor
import Math.CategoryTheory.Opposite

namespace CategoryTheory

variable (α : Sort u) (β : Sort v) [Category α] [Category β]

def Presheaf := Functor (Category.op α) β

end CategoryTheory
