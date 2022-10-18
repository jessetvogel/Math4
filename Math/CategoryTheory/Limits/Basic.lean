import Math.CategoryTheory.Limits.Cone

namespace CategoryTheory

structure Limit {C D : Category} (F : Functor C D) where
  cone : Cone F
  term : @terminal (CatCone F) cone

end CategoryTheory
