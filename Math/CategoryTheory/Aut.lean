import Math.CategoryTheory.Basic
import Math.Algebra.Group.Basic

open Algebra

namespace CategoryTheory

open Category

variable {α : Type u} [Category α]

/-- An automorphism of `X`. -/
def Aut (X : α) := Iso X X

instance AutGroup (X : α) : Group.{u} (Aut.{u, u + 1} X) where
  one := Iso.id X
  mul g f := Iso.comp g f
  mul_assoc h g f := by {
    show Iso.mk (h.hom ∘ g.hom ∘ f.hom) ((f.inv ∘ g.inv) ∘ h.inv) _ _ = Iso.mk ((h.hom ∘ g.hom) ∘ f.hom) (f.inv ∘ g.inv ∘ h.inv) _ _;
    congr 1; simp; simp;
  }
  mul_one f := by {
    show Iso.mk (f.hom ∘ 𝟙 X) (𝟙 X ∘ f.inv) _ _ = f;
    congr; simp; simp;
  }
  one_mul f := by {
    show Iso.mk (𝟙 X ∘ f.hom) (f.inv ∘ 𝟙 X) _ _ = f;
    congr; simp; simp;
  }
  inv := Iso.inverse
  mul_inv f := by {
    show Iso.mk (f.hom ∘ f.inv) (f.hom ∘ f.inv) _ _ = Iso.mk (𝟙 X) (𝟙 X) _ _;
    congr;
    exact f.comp_inv;
    exact f.comp_inv;
  }

end CategoryTheory
