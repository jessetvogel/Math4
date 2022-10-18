import Math.CategoryTheory.Adjunction.Basic
import Math.CategoryTheory.Monad.Basic

namespace CategoryTheory.Adjunction

variable [Category α] [Category β] {F : Functor α β} {G : Functor β α} (adj : F ⊣ G)

def unit (adj : F ⊣ G) : Functor.id α ⇒ G.comp F where
  app X := adj.tr $ 𝟙 (F.obj X)
  natural f := by unfold Functor.id, Functor.comp; simp

def counit (adj : F ⊣ G) : F.comp G ⇒ Functor.id β where
  app Y := adj.tr' $ 𝟙 (G.obj Y)
  natural g := by unfold Functor.id, Functor.comp; simp

def monad {F : Functor α β} (adj : F ⊣ G) : Monad α where
  T := G.comp F
  μ := (adj.counit.whisker_right F).whisker_left G
  η := adj.unit
  assoc X := by {
    unfold NatTrans.whisker_left, NatTrans.whisker_right, Functor.comp, Adjunction.counit; dsimp;
    rw [← G.map_comp, ← G.map_comp]; -- unmap G
    simp;
  }
  mul_one X := by unfold NatTrans.whisker_left, NatTrans.whisker_right, Adjunction.counit, Adjunction.unit, Functor.id, Functor.comp; simp
  one_mul X := by {
    unfold NatTrans.whisker_left, NatTrans.whisker_right, Adjunction.counit, Adjunction.unit, Functor.id, Functor.comp;
    dsimp;
    rw [← G.map_comp, ← G.map_id (F.obj X)];
    congr;
    simp;
  }

end CategoryTheory.Adjunction
