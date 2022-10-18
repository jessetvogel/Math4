import Math.CategoryTheory.Basic
import Math.CategoryTheory.Functor

open CategoryTheory.Category

namespace CategoryTheory

variable [Category α] [Category β] [Category γ]

structure NatTrans (F G : Functor α β) where
  app : ∀ (X : α), hom (F.obj X) (G.obj X)
  natural : ∀ {X Y : α} (f : hom X Y), app Y ∘ F.map f = G.map f ∘ app X := by simp

infixr:80 " ⇒ " => NatTrans

namespace NatTrans

/-- The identity natural transformation `F ⇒ F`. -/
def id (F : Functor α β) : F ⇒ F where
  app X := 𝟙 (F.obj X)

def comp {F G H : Functor α β} (ν : G ⇒ H) (μ : F ⇒ G) : F ⇒ H where
  app X := ν.app X ∘ μ.app X
  natural f := by rw [← comp_assoc, ← ν.natural, comp_assoc, μ.natural, comp_assoc]

def whisker_left {F G : Functor α β} (μ : F ⇒ G) (H : Functor β γ) : (H.comp F) ⇒ (H.comp G) where
  app X := H.map (μ.app X)
  natural f := by dsimp [Functor.comp]; rw [← H.map_comp, ← H.map_comp, μ.natural]

def whisker_right {F G : Functor β γ} (μ : F ⇒ G) (H : Functor α β) : (F.comp H) ⇒ (G.comp H) where
  app X := μ.app (H.obj X)
  natural f := by dsimp[Functor.comp]; rw [μ.natural];

end NatTrans

/-- The category of functors from `α` to `β`. -/
instance CatFunctor : Category (Functor α β) where
  hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.comp
  comp_id := λ {F G} μ => by dsimp; unfold NatTrans.comp, NatTrans.id; congr; funext _; rw [comp_id]
  id_comp := λ μ => by dsimp; unfold NatTrans.comp, NatTrans.id; congr; funext _; rw [id_comp]
  comp_assoc := λ μ ν η => by dsimp; unfold NatTrans.comp; dsimp; congr; funext _; rw [comp_assoc]

/-- A natural isomorphism from `F` to `G` is an isomorphism in the category of functors. -/
def NatIso (F G : Functor α β) := Iso F G

end CategoryTheory
