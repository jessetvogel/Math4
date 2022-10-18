import Math.CategoryTheory.Functor

namespace CategoryTheory

open Category

variable [Category α] (F : Functor α (Type u))

def Elements := Σ X, F.obj X

def CatElements : Category (Elements F) where
  hom X Y := { f : hom X.fst Y.fst // (F.map f) X.snd = Y.snd }
  id X := ⟨𝟙 X.fst, by rw [Functor.map_id]; rfl⟩
  comp {X Y Z} g f := ⟨g.val ∘ f.val, by {
    rw [Functor.map_comp];
    show F.map g.val (F.map f.val (X.snd)) = Z.snd;
    rw [f.2, g.2];
  }⟩
  comp_id f := by simp
  id_comp f := by simp
  comp_assoc h g f := by simp

end CategoryTheory
