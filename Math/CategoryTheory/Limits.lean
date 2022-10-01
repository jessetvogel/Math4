import Math.CategoryTheory.Cone

namespace CategoryTheory

def limit (F : Functor C D) (c : (CatCone F).obj) : Prop := Category.terminal c

end CategoryTheory
