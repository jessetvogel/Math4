import Math.CategoryTheory.NatTrans
import Math.Data.Equiv

namespace CategoryTheory

open Category

variable [Category α] [Category β]

structure Adjunction (F : Functor α β) (G : Functor β α) where
  equiv : ∀ (X : α) (Y : β), hom (F.obj X) Y ≃ hom X (G.obj Y)
  natural : ∀ (f : hom X X') (g : hom Y Y') (h : hom (F.obj X') Y), G.map g ∘ (equiv _ _).map h ∘ f = (equiv _ _).map (g ∘ h ∘ F.map f)

infix:80 " ⊣ " => Adjunction

namespace Adjunction

variable {F : Functor α β} {G : Functor β α}
variable (adj : F ⊣ G)

def tr  (f : hom (F.obj X) Y) := (adj.equiv _ _).map f
def tr' (g : hom X (G.obj Y)) := (adj.equiv _ _).inv g

@[simp]
theorem tr_tr'_inv (g : hom X (G.obj Y)) : adj.tr (adj.tr' g) = g := by unfold tr', tr; simp;

@[simp]
theorem tr'_tr_inv (f : hom (F.obj X) Y) : adj.tr' (adj.tr f) = f := by unfold tr', tr; simp;

@[simp]
theorem natural₁ (f : hom X X') (h : hom (F.obj X') Y) : adj.tr h ∘ f = adj.tr (h ∘ F.map f) := by {
  have q := adj.natural f (𝟙 Y) h; simp at q; exact q;
}

@[simp]
theorem natural₂ (g : hom Y Y') (h : hom (F.obj X) Y) : G.map g ∘ adj.tr h = adj.tr (g ∘ h) := by {
  have q := adj.natural (𝟙 X) g h; simp at q; exact q;
}

theorem natural' (f : hom X X') (g : hom Y Y') (h : hom X' (G.obj Y)) : g ∘ (adj.tr' h ∘ F.map f) = adj.tr' (G.map g ∘ h ∘ f) := by {
  have q : adj.tr' (adj.tr (g ∘ adj.tr' h ∘ F.map f)) = adj.tr' (adj.tr (adj.tr' (G.map g ∘ h ∘ f))) := by {
    rw [← adj.natural₂, ← adj.natural₁];
    simp;
  }
  simp at q;
  exact q;
}

@[simp]
theorem natural'₁ (f : hom X X') (h : hom X' (G.obj Y)) : adj.tr' h ∘ F.map f = adj.tr' (h ∘ f) := by {
  have q := adj.natural' f (𝟙 Y) h; simp at q; exact q;
}

@[simp]
theorem natural'₂ (g : hom Y Y') (h : hom X (G.obj Y)) : g ∘ (adj.tr' h) = adj.tr' (G.map g ∘ h) := by {
  have q := natural' adj (𝟙 X) g h; simp at q; exact q;
}

end Adjunction

end CategoryTheory
