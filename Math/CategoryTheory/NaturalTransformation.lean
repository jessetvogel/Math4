import Math.CategoryTheory.Category
import Math.CategoryTheory.Functor

namespace CategoryTheory

structure NaturalTransformation (F G : Functor C D) :=
  map     : ∀ X, D.hom (F.obj X) (G.obj X)
  natural : ∀ {X Y} (f : C.hom X Y), (map Y) ∘ (F.hom f) = (G.hom f) ∘ (map X) := by simp

infix:80 " ⇒ " => NaturalTransformation

namespace NaturalTransformation

def id (F : Functor C D) : F ⇒ F := {
  map := λ X => D.id (F.obj X),
}

def comp {F G H : Functor C D} (ν : G ⇒ H) (μ : F ⇒ G) : F ⇒ H := {
  map := λ X => D.comp (ν.map X) (μ.map X),
  natural := λ f => by rw [← D.assoc, ← ν.natural, D.assoc, μ.natural, D.assoc],
}

def whisker_left {F G : Functor C D} (μ : F ⇒ G) (H : Functor D E) : (H.comp F) ⇒ (H.comp G) := {
  map := λ X => H.hom (μ.map X),
  natural := λ f => by unfold Functor.comp; rw [← H.map_comp, ← H.map_comp, μ.natural],
}

def whisker_right {F G : Functor C D} (μ : F ⇒ G) (H : Functor E C) : (F.comp H) ⇒ (G.comp H) := {
  map := λ X => μ.map (H.obj X),
  natural := λ f => by unfold Functor.comp; rw [μ.natural],
}

end NaturalTransformation

def CatFunctor (C D : Category) : Category := {
  obj := Functor C D,
  hom := NaturalTransformation,
  id := NaturalTransformation.id,
  comp := NaturalTransformation.comp,
  comp_id := λ {F G} μ => by dsimp; unfold NaturalTransformation.comp, NaturalTransformation.id; congr; funext _; rw [D.comp_id],
  id_comp := λ μ => by dsimp; unfold NaturalTransformation.comp, NaturalTransformation.id; congr; funext _; rw [D.id_comp],
  assoc := λ μ ν η => by dsimp; unfold NaturalTransformation.comp; dsimp; congr; funext _; rw [D.assoc],
}

end CategoryTheory
