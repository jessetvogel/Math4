import Math.CategoryTheory.Functor

namespace CategoryTheory

def Elements (F : Functor C CatType) := Σ X, F.obj X

def CatElements (F : Functor C CatType) : Category := {
  obj := Elements F,
  hom := λ X Y => { f : C.hom X.1 Y.1 // (F.hom f) X.2 = Y.2 },
  id := λ X => ⟨C.id X.1, by rw [Functor.map_id]; unfold CatType; dsimp⟩,
  comp := λ g f => ⟨g.1 ∘ f.1, by rw [Functor.map_comp]; unfold CatType; dsimp; rw [f.2, g.2]⟩,
  comp_id := λ f => by simp,
  id_comp := λ f => by simp,
  assoc := λ h g f => by simp,
}

end CategoryTheory
