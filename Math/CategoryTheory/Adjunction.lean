import Math.CategoryTheory.Category
import Math.CategoryTheory.Functor
import Math.CategoryTheory.NaturalTransformation
import Math.Data.Equiv

namespace CategoryTheory

structure Adjunction (F : Functor C D) (G : Functor D C) :=
  equiv : ∀ X Y, D.hom (F.obj X) Y ≃ C.hom X (G.obj Y)
  natural : ∀ (f : C.hom X X') (g : D.hom Y Y') (h : D.hom (F.obj X') Y), G.hom g ∘ (equiv _ _).to h ∘ f = (equiv _ _).to (g ∘ h ∘ F.hom f)

infix:80 " ⊣ " => Adjunction

namespace Adjunction

variable {F : Functor C D} {G : Functor D C}

def tr (adj : F ⊣ G) (f : D.hom (F.obj X) Y) := (adj.equiv _ _).to f
def tr' (adj : F ⊣ G) (g : C.hom X (G.obj Y)) := (adj.equiv _ _).inv g

@[simp]
theorem tr_tr'_inv (adj : F ⊣ G) (g : C.hom X (G.obj Y)) : adj.tr (adj.tr' g) = g := by unfold tr', tr; simp;

@[simp]
theorem tr'_tr_inv (adj : F ⊣ G) (f : D.hom (F.obj X) Y) : adj.tr' (adj.tr f) = f := by unfold tr', tr; simp;

@[simp]
theorem natural₁ (adj : F ⊣ G) (f : C.hom X X') (h : D.hom (F.obj X') Y) : adj.tr h ∘ f = adj.tr (h ∘ F.hom f) := by {
  have q := adj.natural f (D.id Y) h; simp at q; exact q;
}

@[simp]
theorem natural₂ (adj : F ⊣ G) (g : D.hom Y Y') (h : D.hom (F.obj X) Y) : G.hom g ∘ adj.tr h = adj.tr (g ∘ h) := by {
  have q := adj.natural (C.id X) g h; simp at q; exact q;
}

theorem natural' (adj : F ⊣ G) (f : C.hom X X') (g : D.hom Y Y') (h : C.hom X' (G.obj Y)) : g ∘ (adj.tr' h ∘ F.hom f) = adj.tr' (G.hom g ∘ h ∘ f) := by {
  have q : adj.tr' (adj.tr (g ∘ adj.tr' h ∘ F.hom f)) = adj.tr' (adj.tr (adj.tr' (G.hom g ∘ h ∘ f))) := by {
    rw [← adj.natural₂, ← adj.natural₁];
    simp;
  }
  simp at q;
  exact q;
}

@[simp]
theorem natural'₁ (adj : F ⊣ G) (f : C.hom X X') (h : C.hom X' (G.obj Y)) : adj.tr' h ∘ F.hom f = adj.tr' (h ∘ f) := by {
  have q := adj.natural' f (D.id Y) h; simp at q; exact q;
}

@[simp]
theorem natural'₂ (adj : F ⊣ G) (g : D.hom Y Y') (h : C.hom X (G.obj Y)) : g ∘ (adj.tr' h) = adj.tr' (G.hom g ∘ h) := by {
  have q := natural' adj (C.id X) g h; simp at q; exact q;
}

def unit (adj : F ⊣ G) : Functor.id C ⇒ G.comp F := {
  map := λ X => adj.tr (D.id (F.obj X)),
  natural := λ f => by unfold Functor.id, Functor.comp; simp,
}

def counit (adj : F ⊣ G) : F.comp G ⇒ Functor.id D := {
  map := λ Y => adj.tr' (C.id (G.obj Y)),
  natural := λ g => by unfold Functor.id, Functor.comp; simp,
}

end Adjunction

end CategoryTheory
