import Math.CategoryTheory.Category
import Math.CategoryTheory.Functor
import Math.CategoryTheory.NaturalTransformation
import Math.CategoryTheory.Adjunction

namespace CategoryTheory

structure Monad (C : Category) :=
  T : Functor C C
  μ : T.comp T ⇒ T
  η : Functor.id C ⇒ T
  assoc : ∀ X, μ.map X ∘ T.hom (μ.map X) = μ.map X ∘ μ.map (T.obj X)
  mul_one : ∀ X, μ.map X ∘ η.map (T.obj X) = C.id (T.obj X)
  one_mul : ∀ X, μ.map X ∘ T.hom (η.map X) = C.id (T.obj X)

attribute [simp] Monad.assoc Monad.mul_one Monad.one_mul

def Adjunction.monad {C D : Category} {F : Functor C D} {G : Functor D C} (adj : F ⊣ G) : Monad C := {
  T := G.comp F,
  μ := ((adj.counit).whisker_right F).whisker_left G,
  η := adj.unit,
  assoc := λ X => by {
    unfold NaturalTransformation.whisker_left, NaturalTransformation.whisker_right, Functor.comp, Adjunction.counit;
    rw [← G.map_comp, ← G.map_comp]; -- unmap G
    simp;
  },
  mul_one := λ X => by unfold NaturalTransformation.whisker_left, NaturalTransformation.whisker_right, Adjunction.counit, Adjunction.unit, Functor.id, Functor.comp; simp,
  one_mul := λ X => by {
    unfold NaturalTransformation.whisker_left, NaturalTransformation.whisker_right, Adjunction.counit, Adjunction.unit, Functor.id, Functor.comp;
    simp;
    rw [← G.map_comp, ← G.map_id (F.obj X)];
    congr;
    simp;
  },
}

end CategoryTheory
