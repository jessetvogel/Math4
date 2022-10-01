import Math.CategoryTheory.Category
import Math.CategoryTheory.Functor
import Math.CategoryTheory.NaturalTransformation

namespace CategoryTheory

structure Cone (F : Functor C D) where
  X : D.obj
  μ : (Functor.const C obj) ⇒ F

structure ConeHom {F : Functor C D} (c c' : Cone F) where
  hom  : D.hom c.X c'.X
  comm : ∀ Y, (c'.μ.map Y) ∘ hom = c.μ.map Y

def ConeHomId {F : Functor C D} (c : Cone F) : ConeHom c c := {
  hom := D.id c.X,
  comm := λ Y => by rw [D.comp_id],
}

def ConeHomComp {F : Functor C D} {c c' c'' : Cone F} (g : ConeHom c' c'') (f : ConeHom c c') : ConeHom c c'' := {
  hom := g.hom ∘ f.hom,
  comm := λ Y => by rw [← D.assoc, g.comm, f.comm],
}

def CatCone (F : Functor C D) : Category := {
  obj := Cone F,
  hom := ConeHom,
  id := ConeHomId,
  comp := ConeHomComp,
  comp_id := λ f => by unfold ConeHomId, ConeHomComp; dsimp; congr; rw [D.comp_id],
  id_comp := λ f => by unfold ConeHomId, ConeHomComp; dsimp; congr; rw [D.id_comp],
  assoc := λ h g f => by dsimp; unfold ConeHomComp; dsimp; congr; rw [D.assoc],
}

end CategoryTheory
