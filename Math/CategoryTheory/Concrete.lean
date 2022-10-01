import Math.CategoryTheory.Functor

namespace CategoryTheory

structure ConcreteCategory where
  cat      : Category
  forget   : Functor cat CatType
  faithful : forget.faithful

end CategoryTheory
