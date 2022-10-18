import Math.CategoryTheory.Basic
import Math.SetTheory.Basic

open SetTheory

namespace CategoryTheory

open Category

variable [Category α]

structure Sieve (X : α) where
  maps : ∀ {Y : α}, Set (hom Y X)
  comp : ∀ {Y Z : α} {f : hom Y X} (_ : f ∈ maps) (g : hom Z Y), f ∘ g ∈ maps

namespace Sieve

def max (X : α) : Sieve X where
  maps := Set.univ _
  comp _ _ := by trivial

def pullback {X : α} (S : Sieve X) (f : hom Y X) : Sieve Y where
  maps g := f ∘ g ∈ S.maps
  comp {Y Z j} hj g := by {
    show f ∘ (j ∘ g) ∈ S.maps;
    rw [← comp_assoc];
    exact S.comp hj _;
  }

def subsieve {X : α} (R S : Sieve X) := ∀ {Y : α} {g : hom Y X}, g ∈ R.maps → g ∈ S.maps

def inter {X : α} (R S : Sieve X) : Sieve X where
  maps := R.maps ∩ S.maps
  comp := λ hf _ => ⟨R.comp (hf.1) _, S.comp (hf.2) _⟩

instance (α : Type u) [Category α] {X : α} : SetTheory.Inter (Sieve X) where
  inter := inter

--

@[simp]
theorem pullback_id {X : α} (S : Sieve X) : S.pullback (𝟙 X) = S := by {
  unfold pullback;
  congr;
  funext _ _;
  rw [id_comp]; rfl;
}

end Sieve

end CategoryTheory
